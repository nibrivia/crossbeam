//! The implementation is based on Dmitry Vyukov's bounded MPMC queue.
//!
//! Source:
//!   - http://www.1024cores.net/home/lock-free-algorithms/queues/bounded-mpmc-queue
//!
//! Copyright & License:
//!   - Copyright (c) 2010-2011 Dmitry Vyukov
//!   - Simplified BSD License and Apache License, Version 2.0
//!   - http://www.1024cores.net/home/code-license

use std::cell::{Cell, UnsafeCell};
use std::error;
use std::fmt;
use std::marker::PhantomData;
use std::mem;
use std::ptr;
use std::sync::atomic::{self, AtomicUsize, Ordering};
use std::sync::Arc;

use crossbeam_utils::{Backoff, CachePadded};

/// A slot in a queue.
struct Slot<T> {
    /// The current stamp.
    ///
    /// If the stamp equals the tail, this node will be next written to. If it equals head + 1,
    /// this node will be next read from.
    stamp: AtomicUsize,

    /// The value in this slot.
    value: UnsafeCell<T>,
}

/// A bounded multi-producer multi-consumer queue.
///
/// This queue allocates a fixed-capacity buffer on construction, which is used to store pushed
/// elements. The queue cannot hold more elements than the buffer allows. Attempting to push an
/// element into a full queue will fail. Having a buffer allocated upfront makes this queue a bit
/// faster than [`SegQueue`].
///
/// [`SegQueue`]: struct.SegQueue.html
///
/// # Examples
///
/// ```
/// use crossbeam_queue::bounded::{Queue, PushError};
///
/// let q = Queue::new(2);
///
/// assert_eq!(q.push('a'), Ok(()));
/// assert_eq!(q.push('b'), Ok(()));
/// assert_eq!(q.push('c'), Err(PushError('c')));
/// assert_eq!(q.pop(), Ok('a'));
/// ```
pub struct Queue<T> {
    /// The head of the queue.
    ///
    /// This value is a "stamp" consisting of an index into the buffer and a lap, but packed into a
    /// single `usize`. The lower bits represent the index, while the upper bits represent the lap.
    ///
    /// Elements are popped from the head of the queue.
    head: CachePadded<AtomicUsize>,

    /// The tail of the queue.
    ///
    /// This value is a "stamp" consisting of an index into the buffer and a lap, but packed into a
    /// single `usize`. The lower bits represent the index, while the upper bits represent the lap.
    ///
    /// Elements are pushed into the tail of the queue.
    tail: CachePadded<AtomicUsize>,

    /// The buffer holding slots.
    buffer: *mut Slot<T>,

    /// The queue capacity.
    cap: usize,

    /// A stamp with the value of `{ lap: 1, index: 0 }`.
    one_lap: usize,

    /// Indicates that dropping an `Queue<T>` may drop elements of type `T`.
    _marker: PhantomData<T>,
}

unsafe impl<T: Send> Sync for Queue<T> {}
unsafe impl<T: Send> Send for Queue<T> {}

impl<T> Queue<T> {
    /// Creates a new bounded queue with the given capacity.
    ///
    /// # Panics
    ///
    /// Panics if the capacity is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::Queue;
    ///
    /// let q = Queue::<i32>::new(100);
    /// ```
    pub fn new(cap: usize) -> Queue<T> {
        assert!(cap > 0, "capacity must be non-zero");

        // Head is initialized to `{ lap: 0, index: 0 }`.
        // Tail is initialized to `{ lap: 0, index: 0 }`.
        let head = 0;
        let tail = 0;

        // Allocate a buffer of `cap` slots.
        let buffer = {
            let mut v = Vec::<Slot<T>>::with_capacity(cap);
            let ptr = v.as_mut_ptr();
            mem::forget(v);
            ptr
        };

        // Initialize stamps in the slots.
        for i in 0..cap {
            unsafe {
                // Set the stamp to `{ lap: 0, index: i }`.
                let slot = buffer.add(i);
                ptr::write(&mut (*slot).stamp, AtomicUsize::new(i));
            }
        }

        // One lap is the smallest power of two greater than `cap`.
        let one_lap = (cap + 1).next_power_of_two();

        Queue {
            buffer,
            cap,
            one_lap,
            head: CachePadded::new(AtomicUsize::new(head)),
            tail: CachePadded::new(AtomicUsize::new(tail)),
            _marker: PhantomData,
        }
    }

    pub fn split(self) -> (Producer<T>, Consumer<T>) {
        let inner = Arc::new(self);
        let p = Producer {
            inner: inner.clone(),
            multi: Cell::new(false),
        };
        let c = Consumer {
            inner,
            multi: Cell::new(false),
        };
        (p, c)
    }

    /// Attempts to push an element into the queue.
    ///
    /// If the queue is full, the element is returned back as an error.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PushError};
    ///
    /// let q = Queue::new(1);
    ///
    /// assert_eq!(q.push(10), Ok(()));
    /// assert_eq!(q.push(20), Err(PushError(20)));
    /// ```
    pub fn push(&self, value: T) -> Result<(), PushError<T>> {
        self.push_internal(value, true)
    }

    fn push_internal(&self, value: T, multi: bool) -> Result<(), PushError<T>> {
        let backoff = Backoff::new();
        let mut tail = self.tail.load(Ordering::Relaxed);

        loop {
            // Deconstruct the tail.
            let index = tail & (self.one_lap - 1);
            let lap = tail & !(self.one_lap - 1);

            // Inspect the corresponding slot.
            let slot = unsafe { &*self.buffer.add(index) };
            let stamp = slot.stamp.load(Ordering::Acquire);

            // If the tail and the stamp match, we may attempt to push.
            if tail == stamp {
                let new_tail = if index + 1 < self.cap {
                    // Same lap, incremented index.
                    // Set to `{ lap: lap, index: index + 1 }`.
                    tail + 1
                } else {
                    // One lap forward, index wraps around to zero.
                    // Set to `{ lap: lap.wrapping_add(1), index: 0 }`.
                    lap.wrapping_add(self.one_lap)
                };

                if multi {
                    // Try moving the tail forward.
                    if let Err(t) = self.tail.compare_exchange_weak(
                        tail,
                        new_tail,
                        Ordering::SeqCst,
                        Ordering::Relaxed,
                    ) {
                        tail = t;
                        backoff.spin();
                        continue;
                    }
                } else {
                    // Move the tail forward.
                    self.tail.store(new_tail, Ordering::Release);
                }

                // Write the value into the slot and update the stamp.
                unsafe {
                    slot.value.get().write(value);
                }
                slot.stamp.store(tail + 1, Ordering::Release);
                return Ok(());
            } else if stamp.wrapping_add(self.one_lap) == tail + 1 {
                let head = if multi {
                    atomic::fence(Ordering::SeqCst);
                    self.head.load(Ordering::Relaxed)
                } else {
                    self.head.load(Ordering::Acquire)
                };

                // If the head lags one lap behind the tail as well...
                if head.wrapping_add(self.one_lap) == tail {
                    // ...then the queue is full.
                    return Err(PushError(value));
                }

                backoff.spin();

                if multi {
                    tail = self.tail.load(Ordering::Relaxed);
                }
            } else {
                // Snooze because we need to wait for the stamp to get updated.
                backoff.snooze();

                if multi {
                    tail = self.tail.load(Ordering::Relaxed);
                }
            }
        }
    }

    /// Attempts to pop an element from the queue.
    ///
    /// If the queue is empty, an error is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::new(1);
    /// assert_eq!(q.push(10), Ok(()));
    ///
    /// assert_eq!(q.pop(), Ok(10));
    /// assert_eq!(q.pop(), Err(PopError));
    /// ```
    pub fn pop(&self) -> Result<T, PopError> {
        self.pop_internal(true)
    }

    fn pop_internal(&self, multi: bool) -> Result<T, PopError> {
        let backoff = Backoff::new();
        let mut head = self.head.load(Ordering::Relaxed);

        loop {
            // Deconstruct the head.
            let index = head & (self.one_lap - 1);
            let lap = head & !(self.one_lap - 1);

            // Inspect the corresponding slot.
            let slot = unsafe { &*self.buffer.add(index) };
            let stamp = slot.stamp.load(Ordering::Acquire);

            // If the the stamp is ahead of the head by 1, we may attempt to pop.
            if head + 1 == stamp {
                let new_head = if index + 1 < self.cap {
                    // Same lap, incremented index.
                    // Set to `{ lap: lap, index: index + 1 }`.
                    head + 1
                } else {
                    // One lap forward, index wraps around to zero.
                    // Set to `{ lap: lap.wrapping_add(1), index: 0 }`.
                    lap.wrapping_add(self.one_lap)
                };

                if multi {
                    // Try moving the head forward.
                    if let Err(h) = self.head.compare_exchange_weak(
                        head,
                        new_head,
                        Ordering::SeqCst,
                        Ordering::Relaxed,
                    ) {
                        head = h;
                        backoff.spin();
                        continue;
                    }
                } else {
                    // Move the head forward.
                    self.head.store(new_head, Ordering::Release);
                }

                // Read the value from the slot and update the stamp.
                let msg = unsafe { slot.value.get().read() };
                slot.stamp
                    .store(head.wrapping_add(self.one_lap), Ordering::Release);
                return Ok(msg);
            } else if stamp == head {
                let tail = if multi {
                    atomic::fence(Ordering::SeqCst);
                    self.tail.load(Ordering::Relaxed)
                } else {
                    self.tail.load(Ordering::Acquire)
                };

                // If the tail equals the head, that means the channel is empty.
                if tail == head {
                    return Err(PopError);
                }

                backoff.spin();

                if multi {
                    head = self.head.load(Ordering::Relaxed);
                }
            } else {
                // Snooze because we need to wait for the stamp to get updated.
                backoff.snooze();

                if multi {
                    head = self.head.load(Ordering::Relaxed);
                }
            }
        }
    }

    /// Returns the capacity of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::<i32>::new(100);
    ///
    /// assert_eq!(q.capacity(), 100);
    /// ```
    pub fn capacity(&self) -> usize {
        self.cap
    }

    /// Returns `true` if the queue is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::new(100);
    ///
    /// assert!(q.is_empty());
    /// q.push(1).unwrap();
    /// assert!(!q.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        let head = self.head.load(Ordering::SeqCst);
        let tail = self.tail.load(Ordering::SeqCst);

        // Is the tail equal to the head?
        //
        // Note: If the head changes just before we load the tail, that means there was a moment
        // when the channel was not empty, so it is safe to just return `false`.
        tail == head
    }

    /// Returns `true` if the queue is full.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::new(1);
    ///
    /// assert!(!q.is_full());
    /// q.push(1).unwrap();
    /// assert!(q.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        let tail = self.tail.load(Ordering::SeqCst);
        let head = self.head.load(Ordering::SeqCst);

        // Is the head lagging one lap behind tail?
        //
        // Note: If the tail changes just before we load the head, that means there was a moment
        // when the queue was not full, so it is safe to just return `false`.
        head.wrapping_add(self.one_lap) == tail
    }

    /// Returns the number of elements in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::new(100);
    /// assert_eq!(q.len(), 0);
    ///
    /// q.push(10).unwrap();
    /// assert_eq!(q.len(), 1);
    ///
    /// q.push(20).unwrap();
    /// assert_eq!(q.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        loop {
            // Load the tail, then load the head.
            let tail = self.tail.load(Ordering::SeqCst);
            let head = self.head.load(Ordering::SeqCst);

            // If the tail didn't change, we've got consistent values to work with.
            if self.tail.load(Ordering::SeqCst) == tail {
                return self.calculate_len(head, tail);
            }
        }
    }

    fn calculate_len(&self, head: usize, tail: usize) -> usize {
        let hix = head & (self.one_lap - 1);
        let tix = tail & (self.one_lap - 1);

        if hix < tix {
            tix - hix
        } else if hix > tix {
            self.cap - hix + tix
        } else if tail == head {
            0
        } else {
            self.cap
        }
    }
}

impl<T> Drop for Queue<T> {
    fn drop(&mut self) {
        // Get the index of the head.
        let hix = self.head.load(Ordering::Relaxed) & (self.one_lap - 1);

        // Loop over all slots that hold a message and drop them.
        for i in 0..self.len() {
            // Compute the index of the next slot holding a message.
            let index = if hix + i < self.cap {
                hix + i
            } else {
                hix + i - self.cap
            };

            unsafe {
                self.buffer.add(index).drop_in_place();
            }
        }

        // Finally, deallocate the buffer, but don't run any destructors.
        unsafe {
            Vec::from_raw_parts(self.buffer, 0, self.cap);
        }
    }
}

impl<T> fmt::Debug for Queue<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("Queue { .. }")
    }
}

pub struct Producer<T> {
    inner: Arc<Queue<T>>,
    multi: Cell<bool>,
}

impl<T> Producer<T> {
    /// Attempts to push an element into the queue.
    ///
    /// If the queue is full, the element is returned back as an error.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PushError};
    ///
    /// let q = Queue::new(1);
    ///
    /// assert_eq!(q.push(10), Ok(()));
    /// assert_eq!(q.push(20), Err(PushError(20)));
    /// ```
    pub fn push(&self, value: T) -> Result<(), PushError<T>> {
        self.inner.push_internal(value, self.multi.get())
    }

    /// Returns the capacity of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::<i32>::new(100);
    ///
    /// assert_eq!(q.capacity(), 100);
    /// ```
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Returns `true` if the queue is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::new(100);
    ///
    /// assert!(q.is_empty());
    /// q.push(1).unwrap();
    /// assert!(!q.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        if self.multi.get() {
            self.inner.is_empty()
        } else {
            let head = self.inner.head.load(Ordering::Acquire);
            let tail = self.inner.tail.load(Ordering::Relaxed);

            // Is the tail equal to the head?
            tail == head
        }
    }

    /// Returns `true` if the queue is full.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::new(1);
    ///
    /// assert!(!q.is_full());
    /// q.push(1).unwrap();
    /// assert!(q.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        if self.multi.get() {
            self.inner.is_full()
        } else {
            let tail = self.inner.tail.load(Ordering::Relaxed);
            let head = self.inner.head.load(Ordering::Acquire);

            // Is the head lagging one lap behind tail?
            head.wrapping_add(self.inner.one_lap) == tail
        }
    }

    /// Returns the number of elements in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::new(100);
    /// assert_eq!(q.len(), 0);
    ///
    /// q.push(10).unwrap();
    /// assert_eq!(q.len(), 1);
    ///
    /// q.push(20).unwrap();
    /// assert_eq!(q.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        if self.multi.get() {
            self.inner.len()
        } else {
            let tail = self.inner.tail.load(Ordering::Relaxed);
            let head = self.inner.head.load(Ordering::Acquire);
            self.inner.calculate_len(head, tail)
        }
    }
}

impl<T> Clone for Producer<T> {
    fn clone(&self) -> Producer<T> {
        self.multi.set(true);

        Producer {
            inner: self.inner.clone(),
            multi: Cell::new(true),
        }
    }
}

pub struct Consumer<T> {
    inner: Arc<Queue<T>>,
    multi: Cell<bool>,
}

impl<T> Consumer<T> {
    /// Attempts to pop an element from the queue.
    ///
    /// If the queue is empty, an error is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::new(1);
    /// assert_eq!(q.push(10), Ok(()));
    ///
    /// assert_eq!(q.pop(), Ok(10));
    /// assert_eq!(q.pop(), Err(PopError));
    /// ```
    pub fn pop(&self) -> Result<T, PopError> {
        self.inner.pop_internal(self.multi.get())
    }

    /// Returns the capacity of the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::<i32>::new(100);
    ///
    /// assert_eq!(q.capacity(), 100);
    /// ```
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Returns `true` if the queue is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::new(100);
    ///
    /// assert!(q.is_empty());
    /// q.push(1).unwrap();
    /// assert!(!q.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        if self.multi.get() {
            self.inner.is_empty()
        } else {
            let head = self.inner.head.load(Ordering::Relaxed);
            let tail = self.inner.tail.load(Ordering::Acquire);

            // Is the tail equal to the head?
            tail == head
        }
    }

    /// Returns `true` if the queue is full.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::new(1);
    ///
    /// assert!(!q.is_full());
    /// q.push(1).unwrap();
    /// assert!(q.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        if self.multi.get() {
            self.inner.is_full()
        } else {
            let tail = self.inner.tail.load(Ordering::Acquire);
            let head = self.inner.head.load(Ordering::Relaxed);

            // Is the head lagging one lap behind tail?
            //
            // Note: If the tail changes just before we load the head, that means there was a moment
            // when the queue was not full, so it is safe to just return `false`.
            head.wrapping_add(self.inner.one_lap) == tail
        }
    }

    /// Returns the number of elements in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::bounded::{Queue, PopError};
    ///
    /// let q = Queue::new(100);
    /// assert_eq!(q.len(), 0);
    ///
    /// q.push(10).unwrap();
    /// assert_eq!(q.len(), 1);
    ///
    /// q.push(20).unwrap();
    /// assert_eq!(q.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        if self.multi.get() {
            self.inner.len()
        } else {
            let tail = self.inner.tail.load(Ordering::Acquire);
            let head = self.inner.head.load(Ordering::Relaxed);
            self.inner.calculate_len(head, tail)
        }
    }
}

impl<T> Clone for Consumer<T> {
    fn clone(&self) -> Consumer<T> {
        self.multi.set(true);

        Consumer {
            inner: self.inner.clone(),
            multi: Cell::new(true),
        }
    }
}

/// Error which occurs when popping from an empty queue.
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct PopError;

impl fmt::Debug for PopError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        "PopError".fmt(f)
    }
}

impl fmt::Display for PopError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        "popping from an empty queue".fmt(f)
    }
}

impl error::Error for PopError {}

/// Error which occurs when pushing into a full queue.
#[derive(Clone, Copy, Eq, PartialEq)]
pub struct PushError<T>(pub T);

impl<T> fmt::Debug for PushError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        "PushError(..)".fmt(f)
    }
}

impl<T> fmt::Display for PushError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        "pushing into a full queue".fmt(f)
    }
}

impl<T: Send> error::Error for PushError<T> {}
