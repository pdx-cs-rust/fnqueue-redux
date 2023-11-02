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
        Self { front: Vec::default(), back: Vec::default() }
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
    pub fn pop_front(&mut self) -> Option<T> {
        self.front.pop().or_else(|| {
            while let Some(x) = self.back.pop() {
                self.front.push(x);
            }
            self.front.pop()
        })
    }
}
