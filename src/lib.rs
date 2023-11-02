/*!
Implementation of a "functional queue", a well-known queue
data structure.

Idea: Use two stacks: a stack of queue inputs and a stack of
queue outputs. To push onto the back, push the element onto
the input stack. To pop from the front, pop an element from
the output stack. If the output stack is empty on pop-front,
but the input stack is not, "unstack" the input stack onto
the output stack, then pop from the output stack.
*/

/// "Functional" queue.
pub struct FnQueue<T> {
    front: Vec<T>,
    back: Vec<T>,
}

impl<T> Default for FnQueue<T> {
    fn default() -> Self {
        Self {
            front: Vec::default(),
            back: Vec::default(),
        }
    }
}

impl<T> FnQueue<T> {
    /// Make a new empty queue.
    pub fn new() -> Self {
        Self::default()
    }

    /// Push an element onto the queue.
    pub fn push_back(&mut self, x: T) {
        self.back.push(x);
    }

    /// Try to pop an element from the queue.  Returns
    /// [Some] element if there is something to pop, and
    /// [None] otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fnqueue::FnQueue;
    /// let mut q = FnQueue::new();
    /// q.push_back(1);
    /// q.push_back(2);
    /// assert_eq!(1, q.pop_front().unwrap());
    /// assert_eq!(2, q.pop_front().unwrap());
    /// assert!(q.pop_front().is_none());
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        self.front.pop().or_else(|| {
            while let Some(x) = self.back.pop() {
                self.front.push(x);
            }
            self.front.pop()
        })
    }

    /// Try to look at the front element of the queue.
    /// Returns [Some] element reference if there is
    /// something to see, and [None] otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fnqueue::FnQueue;
    /// let mut q = FnQueue::new();
    /// q.push_back(1);
    /// assert_eq!(&1, q.peek_front().unwrap());
    /// q.push_back(2);
    /// assert_eq!(&1, q.peek_front().unwrap());
    /// let _ = q.pop_front();
    /// assert_eq!(&2, q.peek_front().unwrap());
    /// ```
    pub fn peek_front(&self) -> Option<&T> {
        self.front.last().or_else(|| self.back.first())
    }

    /// Returns `true` if the queue is empty, and `false`
    /// otherwise.
    pub fn is_empty(&self) -> bool {
        self.front.is_empty() && self.back.is_empty()
    }

    /// Returns the count of elements in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fnqueue::FnQueue;
    /// let mut q = FnQueue::new();
    /// q.push_back('a');
    /// assert_eq!(1, q.len());
    /// q.push_back('b');
    /// assert_eq!(2, q.len());
    /// let _ = q.pop_front();
    /// let _ = q.pop_front();
    /// assert_eq!(0, q.len());
    /// ```
    pub fn len(&self) -> usize {
        self.front.len() + self.back.len()
    }
}

#[test]
fn test_push_pop_simple() {
    let mut q = FnQueue::new();
    q.push_back(1u32);
    assert_eq!(Some(1u32), q.pop_front());
    assert_eq!(None, q.pop_front());
}

#[test]
fn test_push_pop_more() {
    let mut q = FnQueue::new();
    for i in 1u32..=6 {
        q.push_back(i);
    }
    for i in 1..=3 {
        assert_eq!(Some(i), q.pop_front());
    }
    for i in 7..=9 {
        q.push_back(i);
    }
    for i in 4..=9 {
        assert_eq!(Some(i), q.pop_front());
    }
    assert_eq!(None, q.pop_front());
}
