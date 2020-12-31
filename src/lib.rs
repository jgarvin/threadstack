//! A more ergonomic and more flexible form of thread local storage.
//!
//! Inspired by the [parameters
//! feature](https://docs.racket-lang.org/reference/parameters.html)
//! from Racket.
//!
//! The general idea is the following. Many applications have
//! "context" variables that are needed by almost every module in the
//! application. It is extremely tedious to pass down these values
//! through every every function in the program. The obvious
//! temptation is to use a global variable instead, but global
//! variables have a bunch of widely known downsides:
//!
//! * They lack thread safety.
//!
//! * They create a hidden side channel between modules in your
//! application that can create "spooky action at a distance."
//!
//! * Because there is only one instance of a global variable modules
//! in the program can fight over what they want the value of it to
//! be.
//!
//! Threadstacks are a middle ground. Essentially instead of having a
//! global variable, you keep a thread local stack of values. You can
//! only refer to the value at the top of the stack, and the borrow
//! checker will guarantee that your reference goes away before the
//! value is popped. You can push new values on the stack, but they
//! automatically expire when the lexical scope containing your push
//! ends. Values on the threadstack are immutable unless you go out of
//! your way to use a type with interior mutability like `Cell` or
//! `RefCell`, so code that wants to customize the value typically
//! will do so by pushing on onto the stack rather than clobbering the
//! existing value as would normally occur with a global variable.
//!
//! This gives you the effect of a global variable that you can
//! temporarily override. Functions that before would have referenced
//! a global variable instead reference the top of the stack, and by
//! pushing a value on the stack before calling said functions you can
//! affect their behavior. However you are unable to affect the
//! behavior when your caller calls those functions because by the
//! time control returns to your caller the lexical scope containing
//! your push will have ended and the value you pushed will have
//! automatically been popped from the stack. This limits the degree
//! to which different modules can step on each other.
//!
//! Because the provided `let_ref_thread_stack_value!` creates
//! references that have a special lifetime tied to the current stack
//! frame, it is not necessary to wrap all code using thread stack
//! values inside a call to something like `my_local_key.with(|data|
//! {...})` like you would have to with the standard `thread_local!`
//! TLS implementation.
use rel_ptr::RelPtr;
use std::cell::UnsafeCell;
use std::thread::LocalKey;

// This is done as a separate macro because it is not possible to hide
// a specific macro rules pattern from the documentation.
//
// https://stackoverflow.com/questions/35537758/is-there-a-way-to-hide-a-macro-pattern-from-docs
#[doc(hidden)]
#[macro_export]
macro_rules! declare_thread_stacks_inner {
    ($(#[$attr:meta])* $vis:vis $name:ident, $t:ty, $init:expr) => {
        thread_local! {
            $(#[$attr])* $vis static $name: $crate::ThreadStackWithInitialValue<$t> = $crate::ThreadStackWithInitialValue::new($init)
        }
    };

    ($(#[$attr:meta])* $vis:vis $name:ident, $t:ty) => {
        thread_local! {
            $(#[$attr])* $vis static $name: $crate::ThreadStack<$t> = $crate::ThreadStack::new();
        }
    };
}

/// Macro used to declare one or more thread stacks. The syntax pretty
/// closely mirrors thread_local! from the standard library, except
/// that the `static` key word is not used.
///
/// # Example
///
/// ```
///    use threadstack::declare_thread_stacks;
///
///    declare_thread_stacks!(
///        FOO: u32 = 0xDEADBEEFu32;
///        pub BAR: u32 = 0xDEADBEEFu32;
///        BUZZ: String;
///    );
///
/// ```
///
/// Note that the value on the right side of the equal sign is only
/// the initial value (which may be overridden by calls to
/// `push_thread_stack_value`). Providing an initial value guarantees
/// that accessing the top of the stack through
/// `let_ref_thread_stack_value` or `clone_thread_stack_value` will
/// never panic. Otherwise they may panic if no value has ever been
/// pushed.
#[macro_export]
macro_rules! declare_thread_stacks {
    // empty (base case for the recursion)
    () => {};

    // process multiple declarations
    ($(#[$attr:meta])* $vis:vis $name:ident: $t:ty = $init:expr; $($rest:tt)*) => (
        $crate::declare_thread_stacks_inner!($(#[$attr])* $vis $name, $t, $init);
        $crate::declare_thread_stacks!($($rest)*);
    );

    // handle a single declaration
    ($(#[$attr:meta])* $vis:vis $name:ident: $t:ty = $init:expr;) => (
        $crate::declare_thread_stacks_inner!($(#[$attr])* $vis $name, $t, $init);
    );

    // process multiple declarations
    ($(#[$attr:meta])* $vis:vis $name:ident: $t:ty; $($rest:tt)*) => (
        $crate::declare_thread_stacks_inner!($(#[$attr])* $vis $name, $t);
        $crate::declare_thread_stacks!($($rest)*);
    );

    // handle a single declaration
    ($(#[$attr:meta])* $vis:vis $name:ident: $t:ty;) => (
        $crate::declare_thread_stacks_inner!($(#[$attr])* $vis $name, $t);
    );
}

// Making this a separate struct lets us have a single
// ThreadStackGuard struct to handle the cases with and without
// initial values.
#[doc(hidden)]
pub struct ThreadStackInner<T> {
    top: UnsafeCell<RelPtr<T>>,
}

/// The container for the underlying array used to implement the stack
/// of values when the stack is not given an initial value (for that
/// see `ThreadStackWithInitialValue`). Generally you will only ever
/// see this type wrapped inside of `std::thread:LocalKey`, and there
/// is never any reason really to use it directly. Instead use
/// `declare_thread_stacks!`, `let_ref_thread_stack_value!`,
/// `push_thread_stack_value!` and `clone_thread_stack_value`.
pub struct ThreadStack<T> {
    inner: ThreadStackInner<T>,
}

/// The container for the underlying array used to implement the stack
/// of values, when in the declaration and initial value for the stack
/// was specified. This is only a separate type from `ThreadStack` so
/// that a branch and possible panic can be omitted for slightly
/// better performance and smaller generated code. Generally you will
/// only ever see this type wrapped inside of `std::thread:LocalKey`,
/// and there is never any reason really to use it directly. Instead
/// use `declare_thread_stacks!`, `let_ref_thread_stack_value!`,
/// `push_thread_stack_value!` and `clone_thread_stack_value`.
pub struct ThreadStackWithInitialValue<T> {
    inner: ThreadStackInner<T>,
    initial: T,
}

#[doc(hidden)]
pub trait IsThreadStack<T> {
    fn get_inner(&self) -> &ThreadStackInner<T>;

    unsafe fn push_value_impl<'a>(&self, new_value: &'a T) -> ThreadStackGuard<'a, T> {
        let inner = self.get_inner();
        let top: &mut RelPtr<T> = &mut *inner.top.get();
        let old_top: RelPtr<T> = *top;
        top.set_unchecked((new_value as *const T) as *mut T);
        ThreadStackGuard {
            previous_top: old_top,
            stack: self.get_inner() as *const ThreadStackInner<T>,
            stack_lifetime_hack: std::marker::PhantomData,
        }
    }

    unsafe fn get_value_impl<'a, 'b>(self: &'b Self, _hack: &'a ()) -> &'a T;
}

impl<T> IsThreadStack<T> for ThreadStack<T> {
    fn get_inner(&self) -> &ThreadStackInner<T> {
        &self.inner
    }

    unsafe fn get_value_impl<'a, 'b>(self: &'b ThreadStack<T>, _hack: &'a ()) -> &'a T {
        let p: &RelPtr<T> = &*self.inner.top.get();
        if p.is_null() {
            panic!("Tried to access threadstack with no initial value and no set value!");
        }
        p.as_ref_unchecked()
    }
}

impl<T> IsThreadStack<T> for ThreadStackWithInitialValue<T> {
    fn get_inner(&self) -> &ThreadStackInner<T> {
        &self.inner
    }

    unsafe fn get_value_impl<'a, 'b>(
        self: &'b ThreadStackWithInitialValue<T>,
        _hack: &'a (),
    ) -> &'a T {
        // Because we were defined with an initial value we know we
        // can always dereference this pointer.
        let p: &RelPtr<T> = &*self.inner.top.get();
        p.as_ref_unchecked()
    }
}

impl<T> ThreadStack<T> {
    // This function should be able to be const but can't be because
    // RelPtr::null() is not const.
    pub fn new() -> Self {
        ThreadStack {
            inner: ThreadStackInner {
                top: UnsafeCell::new(RelPtr::null()),
            },
        }
    }
}

impl<T> ThreadStackWithInitialValue<T> {
    // This function should be able to be const
    // but can't be because of:
    // https://github.com/rust-lang/rust/issues/69908
    #[doc(hidden)]
    pub fn new(initial: T) -> Self {
        let mut s = ThreadStackWithInitialValue {
            inner: ThreadStackInner {
                top: UnsafeCell::new(RelPtr::null()),
            },
            initial,
        };
        let top: &mut RelPtr<T> = unsafe { &mut *s.inner.top.get() };
        unsafe {
            top.set_unchecked(&mut s.initial as *mut T);
        }
        return s;
    }
}

/// Create a local reference to the value at the top of the
/// threadstack. Even though the top value may have been pushed at a
/// much higher layer in the call stack, the reference has a
/// conservative lifetime to guarantee safety -- the same lifetime as
/// a local variable created on the stack where the macro is invoked.
/// If you don't want to have to worry about lifetimes consider using
/// `clone_thread_stack_value` instead.
///
/// Note that this can panic, but only if you did not provide an
/// initial value when you declared your thread stack.
///
/// ```
/// use threadstack::*;
///
/// declare_thread_stacks!(
///     FOO: String = String::from("hello world");
/// );
///
/// let_ref_thread_stack_value!(my_reference, FOO);
/// assert!(my_reference == "hello world");
///
/// {
///     push_thread_stack_value!("hello universe".into(), FOO);
///     let_ref_thread_stack_value!(my_other_reference, FOO);
///     assert!(my_other_reference == "hello universe");
/// }
///
/// assert!(my_reference == "hello world");
/// push_thread_stack_value!("hello galaxy".into(), FOO);
/// assert!(my_reference == "hello world"); // still is reference to old value!
/// let_ref_thread_stack_value!(my_reference, FOO); // shadows the old reference
/// assert!(my_reference == "hello galaxy");
/// ````
#[macro_export]
macro_rules! let_ref_thread_stack_value {
    ($new_variable:ident, $thread_stack:expr) => {
        let stack_lifetime_hack = ();
        let s = &$thread_stack;
        $crate::compile_time_assert_is_thread_stack(s);
        let $new_variable = s.with(|stack| unsafe { stack.get_value_impl(&stack_lifetime_hack) });
    };
}

#[doc(hidden)]
pub fn compile_time_assert_is_thread_stack<U, T: IsThreadStack<U>>(_t: &LocalKey<T>) -> () {
    ()
}

#[doc(hidden)]
pub struct ThreadStackGuard<'a, T> {
    previous_top: RelPtr<T>, // not valid to dereference from here, just a backup!
    stack: *const ThreadStackInner<T>,
    stack_lifetime_hack: std::marker::PhantomData<&'a ()>,
}

impl<'a, T> Drop for ThreadStackGuard<'a, T> {
    fn drop(&mut self) {
        let stack = unsafe { &*self.stack };
        unsafe {
            *stack.top.get() = self.previous_top;
        }
    }
}

/// Clone the value currently at the top of threadstack. This lets you
/// avoid worrying about lifetimes but does require a clone to be
/// made. This can panic only if nothing has been pushed onto the
/// threadstack and it was created without an initial value.
///
/// ```
/// use threadstack::*;
///
/// declare_thread_stacks!(
///     FOO: String = String::from("hello world");
/// );
///
/// assert!(clone_thread_stack_value(&FOO) == "hello world");
/// ````
pub fn clone_thread_stack_value<T: Clone, U: IsThreadStack<T>>(stack: &'static LocalKey<U>) -> T {
    let_ref_thread_stack_value!(the_value, stack);
    the_value.clone()
}

/// Push a new value on the top of the threadstack. This value becomes
/// the value that will be returned by `clone_thread_stack_value` and
/// that `let_ref_thread_stack_value!` will create a reference to. Can
/// only be invoked inside a function, and the effect will last until
/// the end of the current scope. Pushing a new value onto the
/// threadstack will never panic. The assumption is that threadstacks
/// are mostly used for infrequently set context data, or
/// configuration settings that would otherwise be global variables.
///
/// ```
/// use threadstack::*;
///
/// declare_thread_stacks!(
///     FOO: String = String::from("hello world");
/// );
///
/// assert!(clone_thread_stack_value(&FOO) == "hello world");
///
/// {
///     push_thread_stack_value!("hello universe".into(), FOO);
///     assert!(clone_thread_stack_value(&FOO) == "hello universe");
/// }
///
/// assert!(clone_thread_stack_value(&FOO) == "hello world");
/// ````
#[macro_export]
macro_rules! push_thread_stack_value {
    ($new_value:expr, $thread_stack:expr) => {
        let s = &$thread_stack;
        let v = $new_value;
        $crate::compile_time_assert_is_thread_stack(s);
        let _push_guard = s.with(|stack| unsafe { stack.push_value_impl(&v) });
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    declare_thread_stacks!(
        STACK: u32 = 0xDEADBEEFu32;
    );

    #[test]
    fn it_works() {
        let_ref_thread_stack_value!(stack_value, STACK);
        assert!(stack_value == &0xDEADBEEFu32);
        {
            push_thread_stack_value!(stack_value + 1, STACK);
            let_ref_thread_stack_value!(stack_value, STACK);
            assert!(stack_value == &0xDEADBEF0u32);
        }
        let_ref_thread_stack_value!(stack_value, STACK);
        assert!(stack_value == &0xDEADBEEFu32);
        assert!(clone_thread_stack_value(&STACK) == 0xDEADBEEFu32);
    }

    declare_thread_stacks!(
        STARTS_EMPTY: u32;
    );

    #[test]
    #[should_panic(expected = "no initial value")]
    fn no_initial_value_test() {
        let_ref_thread_stack_value!(wont_work, STARTS_EMPTY);
        assert!(wont_work == &100);
    }

    #[test]
    #[should_panic(expected = "no initial value")]
    fn revert_to_no_initial() {
        {
            push_thread_stack_value!(50, STARTS_EMPTY);
        }
        let_ref_thread_stack_value!(wont_work, STARTS_EMPTY);
        assert!(wont_work == &100);
    }

    #[test]
    fn it_works_no_initial() {
        {
            push_thread_stack_value!(50, STARTS_EMPTY);
            let_ref_thread_stack_value!(stack_value, STARTS_EMPTY);
            assert!(stack_value == &50);
        }
        push_thread_stack_value!(51, STARTS_EMPTY);
        let_ref_thread_stack_value!(stack_value, STARTS_EMPTY);
        assert!(stack_value == &51);
        assert!(clone_thread_stack_value(&STARTS_EMPTY) == 51);
        push_thread_stack_value!(52, STARTS_EMPTY);
        let_ref_thread_stack_value!(stack_value, STARTS_EMPTY);
        assert!(stack_value == &52);
        assert!(clone_thread_stack_value(&STARTS_EMPTY) == 52);
    }
}
