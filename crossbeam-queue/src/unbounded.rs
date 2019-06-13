use std::cell::{Cell, UnsafeCell};
use std::error;
use std::fmt;
use std::marker::PhantomData;
use std::mem::{self, ManuallyDrop};
use std::ptr;
use std::sync::atomic::{self, AtomicPtr, AtomicUsize, Ordering};
use std::sync::Arc;

use crossbeam_utils::{Backoff, CachePadded};

// Bits indicating the state of a slot:
// * If a value has been written into the slot, `WRITE` is set.
// * If a value has been read from the slot, `READ` is set.
// * If the block is being destroyed, `DESTROY` is set.
const WRITE: usize = 1;
const READ: usize = 2;
const DESTROY: usize = 4;

// Each block covers one "lap" of indices.
const LAP: usize = 32;
// The maximum number of values a block can hold.
const BLOCK_CAP: usize = LAP - 1;
// How many lower bits are reserved for metadata.
const SHIFT: usize = 1;
// Indicates that the block is not the last one.
const HAS_NEXT: usize = 1;

/// A slot in a block.
struct Slot<T> {
    /// The value.
    value: UnsafeCell<ManuallyDrop<T>>,

    /// The state of the slot.
    state: AtomicUsize,
}

impl<T> Slot<T> {
    /// Waits until a value is written into the slot.
    fn wait_write(&self) {
        let backoff = Backoff::new();
        while self.state.load(Ordering::Acquire) & WRITE == 0 {
            backoff.snooze();
        }
    }
}

/// A block in a linked list.
///
/// Each block in the list can hold up to `BLOCK_CAP` values.
struct Block<T> {
    /// The next block in the linked list.
    next: AtomicPtr<Block<T>>,

    /// Slots for values.
    slots: [Slot<T>; BLOCK_CAP],
}

impl<T> Block<T> {
    /// Creates an empty block that starts at `start_index`.
    fn new() -> Block<T> {
        unsafe { mem::zeroed() }
    }

    /// Waits until the next pointer is set.
    fn wait_next(&self) -> *mut Block<T> {
        let backoff = Backoff::new();
        loop {
            let next = self.next.load(Ordering::Acquire);
            if !next.is_null() {
                return next;
            }
            backoff.snooze();
        }
    }

    /// Sets the `DESTROY` bit in slots starting from `start` and destroys the block.
    unsafe fn destroy(this: *mut Block<T>, start: usize, multi: bool) {
        if multi {
            // It is not necessary to set the `DESTROY` bit in the last slot because that slot has
            // begun destruction of the block.
            for i in start..BLOCK_CAP - 1 {
                let slot = (*this).slots.get_unchecked(i);

                // Mark the `DESTROY` bit if a thread is still using the slot.
                if slot.state.load(Ordering::Acquire) & READ == 0
                    && slot.state.fetch_or(DESTROY, Ordering::AcqRel) & READ == 0
                {
                    // If a thread is still using the slot, it will continue destruction of the block.
                    return;
                }
            }
        }

        // No thread is using the block, now it is safe to destroy it.
        drop(Box::from_raw(this));
    }
}

/// A position in a queue.
struct Position<T> {
    /// The index in the queue.
    index: AtomicUsize,

    /// The block in the linked list.
    block: AtomicPtr<Block<T>>,
}

/// An unbounded multi-producer multi-consumer queue.
///
/// This queue is implemented as a linked list of segments, where each segment is a small buffer
/// that can hold a handful of elements. There is no limit to how many elements can be in the queue
/// at a time. However, since segments need to be dynamically allocated as elements get pushed,
/// this queue is somewhat slower than [`ArrayQueue`].
///
/// [`ArrayQueue`]: struct.ArrayQueue.html
///
/// # Examples
///
/// ```
/// use crossbeam_queue::unbounded::{PopError, Queue};
///
/// let q = Queue::new();
///
/// q.push('a');
/// q.push('b');
///
/// assert_eq!(q.pop(), Ok('a'));
/// assert_eq!(q.pop(), Ok('b'));
/// assert_eq!(q.pop(), Err(PopError));
/// ```
pub struct Queue<T> {
    /// The head of the queue.
    head: CachePadded<Position<T>>,

    /// The tail of the queue.
    tail: CachePadded<Position<T>>,

    /// Indicates that dropping a `Queue<T>` may drop values of type `T`.
    _marker: PhantomData<T>,
}

unsafe impl<T: Send> Send for Queue<T> {}
unsafe impl<T: Send> Sync for Queue<T> {}

impl<T> Queue<T> {
    /// Creates a new unbounded queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::unbounded::Queue;
    ///
    /// let q = Queue::<i32>::new();
    /// ```
    pub fn new() -> Queue<T> {
        Queue {
            head: CachePadded::new(Position {
                block: AtomicPtr::new(ptr::null_mut()),
                index: AtomicUsize::new(0),
            }),
            tail: CachePadded::new(Position {
                block: AtomicPtr::new(ptr::null_mut()),
                index: AtomicUsize::new(0),
            }),
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

    /// Pushes an element into the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::unbounded::Queue;
    ///
    /// let q = Queue::new();
    ///
    /// q.push(10);
    /// q.push(20);
    /// ```
    pub fn push(&self, value: T) {
        self.push_internal(value, true);
    }

    fn push_internal(&self, value: T, multi: bool) {
        let backoff = Backoff::new();
        let mut tail = self.tail.index.load(Ordering::Acquire);
        let mut block = self.tail.block.load(Ordering::Acquire);
        let mut next_block = None;

        loop {
            // Calculate the offset of the index into the block.
            let offset = (tail >> SHIFT) % LAP;

            // If we reached the end of the block, wait until the next one is installed.
            if offset == BLOCK_CAP {
                backoff.snooze();
                tail = self.tail.index.load(Ordering::Acquire);
                block = self.tail.block.load(Ordering::Acquire);
                continue;
            }

            // If we're going to have to install the next block, allocate it in advance in order to
            // make the wait for other threads as short as possible.
            if offset + 1 == BLOCK_CAP && next_block.is_none() {
                next_block = Some(Box::new(Block::<T>::new()));
            }

            // If this is the first push operation, we need to allocate the first block.
            if block.is_null() {
                let new = Box::into_raw(Box::new(Block::<T>::new()));

                if self
                    .tail
                    .block
                    .compare_and_swap(block, new, Ordering::Release)
                    == block
                {
                    self.head.block.store(new, Ordering::Release);
                    block = new;
                } else {
                    next_block = unsafe { Some(Box::from_raw(new)) };
                    tail = self.tail.index.load(Ordering::Acquire);
                    block = self.tail.block.load(Ordering::Acquire);
                    continue;
                }
            }

            let new_tail = tail + (1 << SHIFT);

            if multi {
                // Try moving the tail index forward.
                if let Err(t) = self.tail.index.compare_exchange_weak(
                    tail,
                    new_tail,
                    Ordering::SeqCst,
                    Ordering::Acquire,
                ) {
                    tail = t;
                    block = self.tail.block.load(Ordering::Acquire);
                    backoff.spin();
                    continue;
                }
            } else {
                // Move the tail index forward.
                self.tail.index.store(new_tail, Ordering::Release);
            }

            unsafe {
                // If we've reached the end of the block, install the next one.
                if offset + 1 == BLOCK_CAP {
                    let next_block = Box::into_raw(next_block.unwrap());
                    let next_index = new_tail.wrapping_add(1 << SHIFT);

                    self.tail.block.store(next_block, Ordering::Release);
                    self.tail.index.store(next_index, Ordering::Release);
                    (*block).next.store(next_block, Ordering::Release);
                }

                // Write the value into the slot.
                let slot = (*block).slots.get_unchecked(offset);
                slot.value.get().write(ManuallyDrop::new(value));
                slot.state.fetch_or(WRITE, Ordering::Release);

                return;
            }
        }
    }

    /// Pops an element from the queue.
    ///
    /// If the queue is empty, an error is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::unbounded::{PopError, Queue};
    ///
    /// let q = Queue::new();
    ///
    /// q.push(10);
    /// assert_eq!(q.pop(), Ok(10));
    /// assert_eq!(q.pop(), Err(PopError));
    /// ```
    pub fn pop(&self) -> Result<T, PopError> {
        self.pop_internal(true)
    }

    fn pop_internal(&self, multi: bool) -> Result<T, PopError> {
        let backoff = Backoff::new();
        let mut head = self.head.index.load(Ordering::Acquire);
        let mut block = self.head.block.load(Ordering::Acquire);

        loop {
            // Calculate the offset of the index into the block.
            let offset = (head >> SHIFT) % LAP;

            // If we reached the end of the block, wait until the next one is installed.
            if offset == BLOCK_CAP {
                backoff.snooze();
                head = self.head.index.load(Ordering::Acquire);
                block = self.head.block.load(Ordering::Acquire);
                continue;
            }

            let mut new_head = head + (1 << SHIFT);

            if new_head & HAS_NEXT == 0 {
                let tail = if multi {
                    atomic::fence(Ordering::SeqCst);
                    self.tail.index.load(Ordering::Relaxed)
                } else {
                    self.tail.index.load(Ordering::Acquire)
                };

                // If the tail equals the head, that means the queue is empty.
                if head >> SHIFT == tail >> SHIFT {
                    return Err(PopError);
                }

                // If head and tail are not in the same block, set `HAS_NEXT` in head.
                if (head >> SHIFT) / LAP != (tail >> SHIFT) / LAP {
                    new_head |= HAS_NEXT;
                }
            }

            // The block can be null here only if the first push operation is in progress. In that
            // case, just wait until it gets initialized.
            if block.is_null() {
                backoff.snooze();
                head = self.head.index.load(Ordering::Acquire);
                block = self.head.block.load(Ordering::Acquire);
                continue;
            }

            if multi {
                // Try moving the head index forward.
                if let Err(h) = self.head.index.compare_exchange_weak(
                    head,
                    new_head,
                    Ordering::SeqCst,
                    Ordering::Acquire,
                ) {
                    head = h;
                    block = self.head.block.load(Ordering::Acquire);
                    backoff.spin();
                    continue;
                }
            } else {
                // Move the head index forward.
                self.head.index.store(new_head, Ordering::Release);
            }

            unsafe {
                // If we've reached the end of the block, move to the next one.
                if offset + 1 == BLOCK_CAP {
                    let next = (*block).wait_next();
                    let mut next_index = (new_head & !HAS_NEXT).wrapping_add(1 << SHIFT);
                    if !(*next).next.load(Ordering::Relaxed).is_null() {
                        next_index |= HAS_NEXT;
                    }

                    self.head.block.store(next, Ordering::Release);
                    self.head.index.store(next_index, Ordering::Release);
                }

                // Read the value.
                let slot = (*block).slots.get_unchecked(offset);
                slot.wait_write();

                let m = slot.value.get().read();
                let value = ManuallyDrop::into_inner(m);

                // Destroy the block if we've reached the end, or if another thread wanted to
                // destroy but couldn't because we were busy reading from the slot.
                if offset + 1 == BLOCK_CAP {
                    Block::destroy(block, 0, multi);
                } else if multi && slot.state.fetch_or(READ, Ordering::AcqRel) & DESTROY != 0 {
                    Block::destroy(block, offset + 1, multi);
                }

                return Ok(value);
            }
        }
    }

    /// Returns `true` if the queue is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::unbounded::Queue;
    ///
    /// let q = Queue::new();
    ///
    /// assert!(q.is_empty());
    /// q.push(1);
    /// assert!(!q.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        let head = self.head.index.load(Ordering::SeqCst);
        let tail = self.tail.index.load(Ordering::SeqCst);
        head >> SHIFT == tail >> SHIFT
    }

    /// Returns the number of elements in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::unbounded::{Queue, PopError};
    ///
    /// let q = Queue::new();
    /// assert_eq!(q.len(), 0);
    ///
    /// q.push(10);
    /// assert_eq!(q.len(), 1);
    ///
    /// q.push(20);
    /// assert_eq!(q.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        loop {
            // Load the tail index, then load the head index.
            let tail = self.tail.index.load(Ordering::SeqCst);
            let head = self.head.index.load(Ordering::SeqCst);

            // If the tail index didn't change, we've got consistent indices to work with.
            if self.tail.index.load(Ordering::SeqCst) == tail {
                return self.calculate_len(head, tail);
            }
        }
    }

    fn calculate_len(&self, mut head: usize, mut tail: usize) -> usize {
        // Erase the lower bits.
        tail &= !((1 << SHIFT) - 1);
        head &= !((1 << SHIFT) - 1);

        // Rotate indices so that head falls into the first block.
        let lap = (head >> SHIFT) / LAP;
        tail = tail.wrapping_sub((lap * LAP) << SHIFT);
        head = head.wrapping_sub((lap * LAP) << SHIFT);

        // Remove the lower bits.
        tail >>= SHIFT;
        head >>= SHIFT;

        // Fix up indices if they fall onto block ends.
        if head == BLOCK_CAP {
            head = 0;
            tail -= LAP;
        }
        if tail == BLOCK_CAP {
            tail += 1;
        }

        // Return the difference minus the number of blocks between tail and head.
        tail - head - tail / LAP
    }
}

impl<T> Drop for Queue<T> {
    fn drop(&mut self) {
        let mut head = self.head.index.load(Ordering::Relaxed);
        let mut tail = self.tail.index.load(Ordering::Relaxed);
        let mut block = self.head.block.load(Ordering::Relaxed);

        // Erase the lower bits.
        head &= !((1 << SHIFT) - 1);
        tail &= !((1 << SHIFT) - 1);

        unsafe {
            // Drop all values between `head` and `tail` and deallocate the heap-allocated blocks.
            while head != tail {
                let offset = (head >> SHIFT) % LAP;

                if offset < BLOCK_CAP {
                    // Drop the value in the slot.
                    let slot = (*block).slots.get_unchecked(offset);
                    ManuallyDrop::drop(&mut *(*slot).value.get());
                } else {
                    // Deallocate the block and move to the next one.
                    let next = (*block).next.load(Ordering::Relaxed);
                    drop(Box::from_raw(block));
                    block = next;
                }

                head = head.wrapping_add(1 << SHIFT);
            }

            // Deallocate the last remaining block.
            if !block.is_null() {
                drop(Box::from_raw(block));
            }
        }
    }
}

impl<T> fmt::Debug for Queue<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("Queue { .. }")
    }
}

impl<T> Default for Queue<T> {
    fn default() -> Queue<T> {
        Queue::new()
    }
}

pub struct Producer<T> {
    inner: Arc<Queue<T>>,
    multi: Cell<bool>,
}

impl<T> Producer<T> {
    /// Pushes an element into the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::unbounded::Queue;
    ///
    /// let q = Queue::new();
    ///
    /// q.push(10);
    /// q.push(20);
    /// ```
    pub fn push(&self, value: T) {
        self.inner.push_internal(value, self.multi.get());
    }

    /// Returns `true` if the queue is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::unbounded::Queue;
    ///
    /// let q = Queue::new();
    ///
    /// assert!(q.is_empty());
    /// q.push(1);
    /// assert!(!q.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        if self.multi.get() {
            self.inner.is_empty()
        } else {
            let head = self.inner.head.index.load(Ordering::Acquire);
            let tail = self.inner.tail.index.load(Ordering::Relaxed);
            head >> SHIFT == tail >> SHIFT
        }
    }

    /// Returns the number of elements in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::unbounded::{Queue, PopError};
    ///
    /// let q = Queue::new();
    /// assert_eq!(q.len(), 0);
    ///
    /// q.push(10);
    /// assert_eq!(q.len(), 1);
    ///
    /// q.push(20);
    /// assert_eq!(q.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        if self.multi.get() {
            self.inner.len()
        } else {
            let tail = self.inner.tail.index.load(Ordering::Relaxed);
            let head = self.inner.head.index.load(Ordering::Acquire);
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
    /// Pops an element from the queue.
    ///
    /// If the queue is empty, an error is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::unbounded::{PopError, Queue};
    ///
    /// let q = Queue::new();
    ///
    /// q.push(10);
    /// assert_eq!(q.pop(), Ok(10));
    /// assert_eq!(q.pop(), Err(PopError));
    /// ```
    pub fn pop(&self) -> Result<T, PopError> {
        self.inner.pop_internal(self.multi.get())
    }

    /// Returns `true` if the queue is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::unbounded::Queue;
    ///
    /// let q = Queue::new();
    ///
    /// assert!(q.is_empty());
    /// q.push(1);
    /// assert!(!q.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        if self.multi.get() {
            self.inner.is_empty()
        } else {
            let head = self.inner.head.index.load(Ordering::Relaxed);
            let tail = self.inner.tail.index.load(Ordering::Acquire);
            head >> SHIFT == tail >> SHIFT
        }
    }

    /// Returns the number of elements in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_queue::unbounded::{Queue, PopError};
    ///
    /// let q = Queue::new();
    /// assert_eq!(q.len(), 0);
    ///
    /// q.push(10);
    /// assert_eq!(q.len(), 1);
    ///
    /// q.push(20);
    /// assert_eq!(q.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        if self.multi.get() {
            self.inner.len()
        } else {
            let tail = self.inner.tail.index.load(Ordering::Acquire);
            let head = self.inner.head.index.load(Ordering::Relaxed);
            self.inner.calculate_len(head, tail)
        }
    }
}

impl<T> Clone for Consumer<T> {
    fn clone(&self) -> Consumer<T> {
        if !self.multi.replace(true) {
            let head = self.inner.head.index.load(Ordering::Acquire);
            let block = self.inner.head.block.load(Ordering::Acquire);

            if !block.is_null() {
                // Calculate the offset of the index into the block.
                let offset = (head >> SHIFT) % LAP;

                // Mark all slots up to the offset as read.
                for i in 0..offset {
                    let slot = unsafe { (*block).slots.get_unchecked(i) };
                    slot.state.fetch_or(READ, Ordering::AcqRel);
                }
            }
        }

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
