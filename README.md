# Lock-free Linked List

Based on the Linked List example in Chapter 9 of "Linked Lists: The Role of Locking" book.

Java's [AtomicMarkableReference](https://docs.oracle.com/javase%2F8%2Fdocs%2Fapi%2F%2F/java/util/concurrent/atomic/AtomicMarkableReference.html) was "poorly" ported so I could be able to implement the same data structure in Rust (it requires extra deallocations).
