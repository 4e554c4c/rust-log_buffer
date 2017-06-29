//! `log_buffer` provides a way to record and extract logs without allocation.
//! The [LogBuffer](struct.LogBuffer.html) achieves this by providing a ring
//! buffer, similar to a *nix _dmesg_ facility.
//!
//! # Usage example
//!
//! ```
//! use std::fmt::Write;
//!
//! let mut dmesg = log_buffer::LogBuffer::new([0; 16]);
//! write!(dmesg, "\nfirst\n").unwrap();
//! write!(dmesg, "second\n").unwrap();
//! write!(dmesg, "third\n").unwrap();
//!
//! assert_eq!(dmesg.extract(),
//!            "st\nsecond\nthird\n");
//! assert_eq!(dmesg.extract_lines().collect::<Vec<_>>(),
//!            vec!["second", "third"]);
//! ```
//!
//! # Choices of backing storage
//!
//! Backed by an array:
//!
//! ```
//! let mut dmesg = log_buffer::LogBuffer::new([0; 16]);
//! ```
//!
//! Backed by a mutable slice:
//!
//! ```
//! let mut storage = [0; 16];
//! let mut dmesg = log_buffer::LogBuffer::new(&mut storage);
//! ```
//!
//! Backed by a vector:
//!
//! ```
//! let mut dmesg = log_buffer::LogBuffer::new(vec![0; 16]);
//! ```


#![no_std]
#![cfg_attr(feature = "const_fn", feature(const_fn))]
#![feature(const_fn)]
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering, ATOMIC_BOOL_INIT, ATOMIC_USIZE_INIT};
use core::cell::UnsafeCell;

/// A ring buffer that stores UTF-8 text.
///
/// Anything that implements `AsMut<[u8]>` can be used for backing storage;
/// e.g. `[u8; N]`, `Vec<[u8]>`, `Box<[u8]>`.
#[derive(Debug)]
pub struct LogBuffer<T: AsMut<[u8]>> {
    pub buffer:   UnsafeCell<T>,
    pub position: AtomicUsize,
    pub lock: AtomicBool
}

impl<T: AsMut<[u8]>> LogBuffer<T> {
    /// Creates a new ring buffer, backed by `storage`.
    ///
    /// The buffer is cleared after creation.
    pub fn new(storage: T) -> LogBuffer<T> {
        let cell = UnsafeCell::new(storage);
        let l = unsafe{(*cell.get()).as_mut().len()};
        assert_eq!(0,l & l-1);
        let buffer = LogBuffer { buffer: cell, position: ATOMIC_USIZE_INIT, lock: ATOMIC_BOOL_INIT };
        buffer.clear();
        buffer
    }

    /// Creates a new ring buffer, backed by `storage`.
    ///
    /// The buffer is *not* cleared after creation, and contains whatever is in `storage`.
    /// The `clear()` method should be called before use.
    /// However, this function can be used in a static initializer.
    ///
    /// # Safety
    /// The `storage` passed to this function must have a capacity that is a power of
    /// two.
    #[cfg(feature = "const_fn")]
    pub const unsafe fn uninitialized(storage: T) -> LogBuffer<T> {
        LogBuffer {
            buffer: UnsafeCell::new(storage),
            position: ATOMIC_USIZE_INIT,
            lock: ATOMIC_USIZE_INIT,
        }
    }

    /// Obtains the lock, can block forever.
    fn obtain_lock(&self) {
        while self.lock.compare_and_swap(false,true,Ordering::Relaxed) == true {}
    }
    fn release_lock(&self) {
        self.lock.store(false, Ordering::Relaxed);
    }

    /// Clears the buffer.
    ///
    /// Only the text written after clearing will be read out by a future extraction.
    ///
    /// This function takes O(n) time where n is buffer length.
    pub fn clear(&self) {
        self.obtain_lock();
        let buffer = unsafe {(*self.buffer.get()).as_mut()};
        self.position.store(0, Ordering::Relaxed);
        for b in buffer.iter_mut() {
            // Any non-leading UTF-8 code unit would do, but 0xff looks like an obvious sentinel.
            // Can't be 0x00 since that is a valid codepoint.
            *b = 0xff;
        }
        self.release_lock();
    }

    fn rotate(&self) {
        // Make sure that the lock is aquired.
        assert!(self.lock.load(Ordering::Relaxed));
        // We're rearranging the buffer such that the last written byte is at the last possible
        // index; then we skip all the junk at the start, and only valid UTF-8 should remain.
        let rotate_by = self.position.load(Ordering::Relaxed);
        if rotate_by == 0 {
            return;
        }
        self.position.store(0, Ordering::Relaxed);

        // The Juggling algorithm
        fn gcd(mut a: usize, mut b: usize) -> usize {
            if a < b { core::mem::swap(&mut a, &mut b) }

            while b != 0 {
                let r = a % b;
                a = b;
                b = r;
            }
            a
        }

        let buffer = unsafe{(*self.buffer.get()).as_mut()};
        for i in 0..gcd(buffer.len(), rotate_by) {
          // move i-th values of blocks
          let temp = buffer[i];
          let mut j = i;
          loop {
            let mut k = j + rotate_by;
            if k >= buffer.len() {
                k -= buffer.len()
            }
            if k == i {
                break
            }
            buffer[j] = buffer[k];
            j = k;
          }
          buffer[j] = temp
        }
    }

    /// Extracts the contents of the ring buffer as a string slice, excluding any
    /// partially overwritten UTF-8 code unit sequences at the beginning.
    ///
    /// Extraction rotates the contents of the ring buffer such that all of its
    /// contents becomes contiguous in memory.
    ///
    /// This function takes O(n) time where n is buffer length.
    pub fn extract(&self) -> &str {
        self.obtain_lock();
        self.rotate();

        // Skip any non-leading UTF-8 code units at the start.
        fn is_utf8_leader(byte: u8) -> bool {
            byte & 0b10000000 == 0b00000000 ||
            byte & 0b11100000 == 0b11000000 ||
            byte & 0b11110000 == 0b11100000 ||
            byte & 0b11111000 == 0b11110000
        }

        let buffer = unsafe{(*self.buffer.get()).as_mut()};
        for i in 0..buffer.len() {
            if is_utf8_leader(buffer[i]) {
                self.release_lock();
                return core::str::from_utf8(&buffer[i..]).unwrap()
            }
        }
        self.release_lock();
        ""
    }

    /// Extracts the contents of the ring buffer as an iterator over its lines,
    /// excluding any partially overwritten lines at the beginning.
    ///
    /// The first line written to the ring buffer after clearing it should start
    /// with `'\n'`, or it will be treated as partially overwritten and lost.
    ///
    /// Extraction rotates the contents of the ring buffer such that all of its
    /// contents becomes contiguous in memory.
    ///
    /// This function takes O(n) time where n is buffer length.
    pub fn extract_lines(&mut self) -> core::str::Lines {
        self.obtain_lock();
        self.rotate();

        let buffer = unsafe{ (*self.buffer.get()).as_mut()};
        for i in 0..buffer.len() {
            if i > 0 && buffer[i - 1] == b'\n' {
                let slice = core::str::from_utf8(&buffer[i..]).unwrap();
                self.release_lock();
                return slice.lines()
            }
        }
        self.release_lock();
        return "".lines()
    }
}

// This allows code that owns the LogBuffer to call `Write` functions as well as ones
// that only have references. This must be done to preserve original functionality and
// pass the tests.
impl<T: AsMut<[u8]>> core::fmt::Write for LogBuffer<T> {
    /// Append `s` to the ring buffer.
    ///
    /// This function takes O(n) time where n is the length of `s`
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        (&*self).write_str(s)
    }
}
impl<'a, T: AsMut<[u8]>> core::fmt::Write for &'a LogBuffer<T> {
    /// Append `s` to the ring buffer.
    ///
    /// This function takes O(n) time where n is length of `s`.
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        // wait for a lock that is in process to finish, but do not obtain the lock
        while self.lock.load(Ordering::Relaxed) == true {}

        let buffer = unsafe {(*self.buffer.get()).as_mut()};
        let mut write_ind = self.position.fetch_add(s.len(),Ordering::Relaxed);
        // take the modulo, for powers of two
        let _ = self.position.fetch_and(buffer.len()-1, Ordering::Relaxed);

        for &b in s.as_bytes() {
            buffer[write_ind] = b;
            write_ind = (write_ind + 1) % buffer.len()
        }
        Ok(())
    }
}

// allows the LogBuffer to be used as a static.
unsafe impl<T> core::marker::Sync for LogBuffer<T>
    where T: AsMut<[u8]> {}
