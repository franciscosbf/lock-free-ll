//! Foolish port of Java AtomicMarkableReference.

use std::sync::atomic::{AtomicPtr, Ordering};

/// Drops Box and frees its memory in place.
///
/// Assumes that the given raw pointer is Box.
macro_rules! drop {
    ($ptr:expr) => {
        unsafe {
            drop(Box::from_raw($ptr));
        }
    };
}

struct Pair<T> {
    reference: *const T,
    mark: bool,
}

impl<T> Pair<T> {
    #[inline]
    fn leaked(reference: *const T, mark: bool) -> *mut Self {
        Box::into_raw(Box::new(Self { reference, mark }))
    }
}

#[derive(Debug)]
pub struct AtomicMarkableReference<T> {
    pair: AtomicPtr<Pair<T>>,
}

impl<T> AtomicMarkableReference<T> {
    #[inline]
    pub fn new(reference: *const T, mark: bool) -> Self {
        let pair = AtomicPtr::new(Pair::leaked(reference, mark));

        Self { pair }
    }

    pub fn compare_and_set(
        &self,
        expected_reference: *const T,
        new_reference: *const T,
        expected_mark: bool,
        new_mark: bool,
    ) -> bool {
        let current_pair = self.pair();
        let current_reference = current_pair.reference;
        let current_mark = current_pair.mark;

        expected_reference == current_reference
            && expected_mark == current_mark
            && ((new_reference == current_reference && new_mark == current_mark) || {
                let new_pair = Pair::leaked(new_reference, new_mark);

                self.cas(current_pair, new_pair)
                    .map_err(|_| {
                        drop!(new_pair);
                    })
                    .map(|previous| {
                        drop!(previous);
                    })
                    .is_ok()
            })
    }

    pub fn attempt_mark(&self, expected_reference: *const T, new_mark: bool) -> bool {
        let current_pair = self.pair();
        let current_reference = current_pair.reference;
        let current_mark = current_pair.mark;

        expected_reference == current_reference
            && (new_mark == current_mark || {
                let new_pair = Pair::leaked(expected_reference, new_mark);

                self.cas(current_pair, new_pair)
                    .map_err(|_| {
                        drop!(new_pair);
                    })
                    .map(|previous| {
                        drop!(previous);
                    })
                    .is_ok()
            })
    }

    #[inline]
    pub fn unsafe_reference_set(&self, reference: *const T) {
        unsafe { &mut **self.pair.as_ptr() }.reference = reference;
    }

    #[inline]
    pub fn get(&self) -> (*const T, bool) {
        let Pair { reference, mark } = *self.pair();

        (reference, mark)
    }

    #[inline]
    pub fn reference(&self) -> *const T {
        self.pair().reference
    }

    #[inline]
    fn pair(&self) -> &Pair<T> {
        unsafe { &**self.pair.as_ptr() }
    }

    #[inline]
    fn cas(
        &self,
        current: *const Pair<T>,
        new: *const Pair<T>,
    ) -> Result<*mut Pair<T>, *mut Pair<T>> {
        self.pair.compare_exchange(
            current as *mut Pair<T>,
            new as *mut Pair<T>,
            Ordering::SeqCst,
            Ordering::Relaxed,
        )
    }
}

impl<T> Drop for AtomicMarkableReference<T> {
    fn drop(&mut self) {
        drop!(*self.pair.as_ptr());
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    #[test]
    fn seq_compare_and_set() {
        let zero = &0;
        let one = &1;
        let two = &2;

        let atomic = AtomicMarkableReference::new(zero, false);

        assert!(atomic.compare_and_set(zero, one, false, true));

        let (reference, marked) = atomic.get();

        assert_eq!(reference, one as *const i32);
        assert!(marked);

        assert!(!atomic.compare_and_set(two, zero, true, false));

        let (reference, marked) = atomic.get();

        assert_eq!(reference, one);
        assert!(marked);

        assert!(!atomic.compare_and_set(one, zero, false, true));

        let (reference, marked) = atomic.get();

        assert_eq!(reference, one);
        assert!(marked);

        assert!(atomic.compare_and_set(one, two, true, false));

        let (reference, marked) = atomic.get();

        assert_eq!(reference, two);
        assert!(!marked);
    }

    #[test]
    fn seq_attempt_mark() {
        let zero = &0;
        let one = &1;

        let atomic = AtomicMarkableReference::new(zero, false);

        assert!(atomic.attempt_mark(zero, true));

        let (reference, marked) = atomic.get();

        assert_eq!(reference, zero);
        assert!(marked);

        assert!(!atomic.attempt_mark(one, false));

        let (reference, marked) = atomic.get();

        assert_eq!(reference, zero);
        assert!(marked);

        assert!(atomic.attempt_mark(zero, false));

        let (reference, marked) = atomic.get();

        assert_eq!(reference, zero);
        assert!(!marked);
    }

    #[test]
    fn par_compare_and_set_with_same_marked() {
        let zero = &0;
        let one = &1;
        let two = &2;

        let atomic = Arc::new(AtomicMarkableReference::new(zero, false));
        let catomic = Arc::clone(&atomic);

        let t = std::thread::spawn(move || {
            while !catomic.compare_and_set(one, two, false, false) {
                std::thread::yield_now();
            }
        });

        assert!(atomic.compare_and_set(zero, one, false, false));

        let _ = t.join();

        let (reference, marked) = atomic.get();

        assert_eq!(reference, two);
        assert!(!marked);
    }

    #[test]
    fn par_compare_and_set_with_different_marker() {
        let zero = &0;

        let atomic: Arc<AtomicMarkableReference<i32>> =
            Arc::new(AtomicMarkableReference::new(zero, false));
        let catomic = Arc::clone(&atomic);

        let t = std::thread::spawn(move || {
            while !catomic.compare_and_set(zero, zero, true, false) {
                std::thread::yield_now();
            }
        });

        assert!(atomic.compare_and_set(zero, zero, false, true));

        let _ = t.join();

        let (reference, marked) = atomic.get();

        assert_eq!(reference, zero);
        assert!(!marked);
    }
}
