mod amr;

use std::{
    ops::Deref,
    ptr::NonNull,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

use amr::AtomicMarkableReference;

/// Drop decrements the Arc counter, so memory free happens when counter reaches zero.
///
/// Assumes that the given raw pointer is Arc.
macro_rules! trydrop {
    ($ptr:expr) => {
        unsafe {
            Arc::from_raw($ptr);
        }
    };
}

#[derive(Debug)]
struct NodeContent<K, V> {
    key: K,
    value: V,
}

#[derive(Debug)]
struct Node<K, V> {
    content: Option<NodeContent<K, V>>,
    next: AtomicMarkableReference<Node<K, V>>,
}

impl<K, V> Node<K, V> {
    #[inline]
    fn new(content: Option<NodeContent<K, V>>, next: *const Node<K, V>) -> *const Self {
        Arc::into_raw(Arc::new(Self {
            content,
            next: AtomicMarkableReference::new(next, false),
        }))
    }

    #[inline]
    fn inner(key: K, value: V) -> *const Self {
        Self::new(
            Some(NodeContent { key, value }),
            NonNull::dangling().as_ptr(),
        )
    }

    #[inline]
    fn tail() -> *const Self {
        Self::new(None, NonNull::dangling().as_ptr())
    }

    #[inline]
    fn head(tail: *const Node<K, V>) -> *const Self {
        Self::new(None, tail)
    }
}

#[derive(Debug)]
pub struct RefGuard<'a, K, V> {
    _node: Arc<Node<K, V>>,
    pub value: &'a V,
}

impl<'a, K, V> RefGuard<'a, K, V>
where
    K: 'a,
{
    #[inline]
    fn new(node: Arc<Node<K, V>>) -> Self {
        let _node = node;
        let value = &(unsafe { &*Arc::as_ptr(&_node) })
            .content
            .as_ref()
            .unwrap()
            .value;

        Self { _node, value }
    }
}

struct Window<K, V> {
    pred: *const Node<K, V>,
    curr: *const Node<K, V>,
}

pub struct InnerLinkedList<K, V> {
    head: *const Node<K, V>,
    tail: *const Node<K, V>,
    len: AtomicUsize,
}

impl<K, V> InnerLinkedList<K, V>
where
    K: PartialEq,
{
    #[inline]
    fn new() -> Self {
        let tail = Node::tail();
        let head = Node::head(tail);
        let len = AtomicUsize::new(0);

        Self { head, tail, len }
    }

    pub fn get(&self, key: &K) -> Option<RefGuard<'_, K, V>> {
        let mut curr = unsafe { &*self.head }.next.reference();

        loop {
            if curr == self.tail {
                break;
            }

            let (succ, marked) = unsafe { &*curr }.next.get();

            if unsafe { &*curr }.content.as_ref().unwrap().key == *key {
                if marked {
                    break;
                }

                let node = unsafe {
                    Arc::increment_strong_count(curr);
                    Arc::from_raw(curr)
                };

                let ref_guard = RefGuard::new(node);

                return Some(ref_guard);
            }

            curr = succ;
        }

        None
    }

    pub fn remove(&self, key: &K) -> bool {
        loop {
            let Window { pred, curr } = self.find(key);

            if curr == self.tail {
                return false;
            }

            let succ = unsafe { &*curr }.next.reference();
            if !unsafe { &*curr }.next.attempt_mark(succ, true) {
                continue;
            }

            if unsafe { &*pred }
                .next
                .compare_and_set(curr, succ, false, false)
            {
                trydrop!(curr);
            }

            self.len.fetch_sub(1, Ordering::SeqCst);

            return true;
        }
    }

    pub fn insert(&self, key: K, value: V) -> bool {
        let node = Node::inner(key, value);
        let key = &unsafe { &*node }.content.as_ref().unwrap().key;

        loop {
            let Window { pred, curr } = self.find(key);

            if curr != self.tail {
                return false;
            }

            unsafe { &*node }.next.unsafe_reference_set(curr);
            if unsafe { &*pred }
                .next
                .compare_and_set(curr, node, false, false)
            {
                self.len.fetch_add(1, Ordering::SeqCst);

                return true;
            }
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len.load(Ordering::SeqCst)
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn find(&self, key: &K) -> Window<K, V> {
        'retry: loop {
            let mut pred = self.head;
            let mut curr = unsafe { &*pred }.next.reference(); // tail

            loop {
                let (mut succ, mut marked) = unsafe { &*curr }.next.get();

                while marked {
                    if !unsafe { &*pred }
                        .next
                        .compare_and_set(curr, succ, false, false)
                    {
                        continue 'retry;
                    }

                    trydrop!(curr);

                    curr = succ;
                    (succ, marked) = unsafe { &*curr }.next.get();
                }

                match unsafe { &*curr }.content {
                    Some(ref content) => {
                        if content.key == *key {
                            return Window { pred, curr };
                        }

                        pred = curr;
                        curr = succ;
                    }
                    None => return Window { pred, curr },
                }
            }
        }
    }
}

impl<K, V> Drop for InnerLinkedList<K, V> {
    fn drop(&mut self) {
        let mut curr = self.head;

        loop {
            let next = unsafe { &*curr }.next.reference();

            trydrop!(curr);

            curr = next;

            if curr == self.tail {
                break;
            }
        }

        trydrop!(self.tail);
    }
}

#[derive(Clone)]
pub struct LinkedList<K, V>(Arc<InnerLinkedList<K, V>>);

impl<K, V> LinkedList<K, V>
where
    K: PartialEq,
{
    #[inline]
    pub fn new() -> Self {
        Self(Arc::new(InnerLinkedList::new()))
    }
}

impl<K, V> Default for LinkedList<K, V>
where
    K: PartialEq,
{
    fn default() -> Self {
        LinkedList::new()
    }
}

impl<K, V> Deref for LinkedList<K, V> {
    type Target = InnerLinkedList<K, V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

unsafe impl<K, V> Send for LinkedList<K, V> {}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use claim::{assert_none, assert_ok, assert_some};
    use rand::{thread_rng, Rng};

    use super::*;

    #[test]
    fn seq_empty_list() {
        let l = LinkedList::<u32, u32>::new();

        assert_eq!(l.len(), 0);
        assert!(l.is_empty());
    }

    #[test]
    fn seq_insert() {
        let l = LinkedList::new();

        for i in 1..=3 {
            assert!(l.insert(i, i), "failed to insert {}", i);
            assert_eq!(l.len(), i as usize);
            let ref_guard = assert_some!(l.get(&i));
            assert_eq!(*ref_guard.value, i);
        }
    }

    #[test]
    fn seq_repeated_insert() {
        let l = LinkedList::new();

        for i in 1..=3 {
            assert!(l.insert(i, i), "failed to insert {}", i);
            assert!(!l.insert(i, i), "inserted repeated {}", i);
            assert_eq!(l.len(), i as usize);
            let ref_guard = assert_some!(l.get(&i));
            assert_eq!(*ref_guard.value, i);
        }
    }

    #[test]
    fn seq_remove() {
        let l = LinkedList::new();

        assert!(!l.remove(&1));

        for i in 1..=3 {
            l.insert(i, i);
        }

        for i in 1..=3 {
            assert!(l.remove(&i));
            assert_eq!(l.len(), 3 - i as usize);
            assert_none!(l.get(&i));
        }
    }

    #[test]
    fn seq_remove_first() {
        let l = LinkedList::new();

        l.insert(1, 1);
        l.insert(2, 2);

        assert!(l.remove(&1));
        assert_eq!(l.len(), 1);
        assert_none!(l.get(&1));
        let ref_guard = assert_some!(l.get(&2));
        assert_eq!(*ref_guard.value, 2);
    }

    #[test]
    fn seq_remove_last() {
        let l = LinkedList::new();

        l.insert(1, 1);
        l.insert(2, 2);

        assert!(l.remove(&2));
        assert_eq!(l.len(), 1);
        assert_none!(l.get(&2));
        let ref_guard = assert_some!(l.get(&1));
        assert_eq!(*ref_guard.value, 1);
    }

    #[test]
    fn seq_remove_middle() {
        let l = LinkedList::new();

        l.insert(1, 1);
        l.insert(2, 2);
        l.insert(3, 3);

        assert!(l.remove(&2));
        assert_eq!(l.len(), 2);
        assert_none!(l.get(&2));
        let ref_guard = assert_some!(l.get(&1));
        assert_eq!(*ref_guard.value, 1);
        let ref_guard = assert_some!(l.get(&3));
        assert_eq!(*ref_guard.value, 3);
    }

    #[test]
    fn seq_repeated_remove() {
        let l = LinkedList::new();

        l.insert(1, 1);
        l.insert(2, 2);

        assert!(l.remove(&1));
        assert_eq!(l.len(), 1);
        assert_none!(l.get(&1));

        assert!(!l.remove(&1));
        assert_eq!(l.len(), 1);
        assert_none!(l.get(&1));

        assert!(l.remove(&2));
        assert_eq!(l.len(), 0);
        assert_none!(l.get(&2));

        assert!(!l.remove(&2));
        assert_eq!(l.len(), 0);
        assert_none!(l.get(&2));
    }

    #[test]
    fn seq_interleaved_insert_and_remove() {
        let l = LinkedList::new();

        l.insert(1, 1);
        l.insert(2, 2);
        l.insert(3, 3);

        assert!(l.remove(&2));
        assert_eq!(l.len(), 2);
        assert_none!(l.get(&2));

        l.insert(4, 4);

        assert!(l.remove(&3));
        assert_eq!(l.len(), 2);
        assert_none!(l.get(&3));

        assert!(l.remove(&1));
        assert_eq!(l.len(), 1);
        assert_none!(l.get(&1));

        assert!(l.remove(&4));
        assert_eq!(l.len(), 0);
        assert_none!(l.get(&4));

        assert!(!l.remove(&4));

        l.insert(5, 5);

        assert!(!l.remove(&4));

        assert!(l.remove(&5));
        assert_eq!(l.len(), 0);
        assert_none!(l.get(&5));
    }

    #[test]
    fn par_insertions() {
        let ll = LinkedList::new();

        let l = ll.clone();
        let t1 = std::thread::spawn(move || {
            for i in 0..1000 {
                assert!(l.insert(i, i));
            }
        });

        let l = ll.clone();
        let t2 = std::thread::spawn(move || {
            for i in 1000..2000 {
                assert!(l.insert(i, i));
            }
        });

        let l = ll.clone();
        let t3 = std::thread::spawn(move || {
            for i in 2000..3000 {
                assert!(l.insert(i, i));
            }
        });

        let l = ll.clone();
        let t4 = std::thread::spawn(move || {
            for i in 3000..4000 {
                assert!(l.insert(i, i));
            }
        });

        assert_ok!(t1.join());
        assert_ok!(t2.join());
        assert_ok!(t3.join());
        assert_ok!(t4.join());

        for i in 0..4000 {
            let ref_guard = assert_some!(ll.get(&i));
            assert_eq!(*ref_guard.value, i);
        }
    }

    #[test]
    fn par_insertions_and_removals() {
        let ll = LinkedList::new();

        let l = ll.clone();
        let t1 = std::thread::spawn(move || {
            for i in 0..2500 {
                assert!(l.insert(i, i));
            }
        });

        let l = ll.clone();
        let t2 = std::thread::spawn(move || {
            for i in 2500..5000 {
                assert!(l.insert(i, i));
            }
        });

        let l = ll.clone();
        let t3 = std::thread::spawn(move || {
            let mut removals = vec![];
            let mut rng = thread_rng();

            for _ in 0..5000 {
                let i = rng.gen_range(0..5000);

                if l.remove(&i) {
                    removals.push(i);
                }
            }

            removals
        });

        assert_ok!(t1.join());
        assert_ok!(t2.join());
        let removals = assert_ok!(t3.join());

        for i in &removals {
            assert_none!(ll.get(i));
        }

        let mut merged_removals = HashSet::new();
        for i in &removals {
            assert!(
                merged_removals.insert(*i),
                "{} was removed more than one time",
                i
            );
        }

        assert_eq!(merged_removals.len(), removals.len());

        let remained = 5000 - removals.len();

        assert_eq!(ll.len(), remained);

        for i in 0..5000 {
            if !merged_removals.contains(&i) {
                let ref_guard = assert_some!(ll.get(&i));
                assert_eq!(*ref_guard.value, i);
            }
        }
    }
}
