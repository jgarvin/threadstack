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
use std::cell::UnsafeCell;
use std::mem::MaybeUninit;
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
            $(#[$attr])* $vis static $name: $crate::ThreadStack<$t> = $crate::ThreadStack::new($init);
        }
    }
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
///    );
///
/// ```
/// Note that the value on the right side of the equal sign is only
/// the initial value (which may be overridden by calls to
/// `push_thread_stack_value`).
///
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
    ($(#[$attr:meta])* $vis:vis $name:ident: $t:ty = $init:expr) => (
        $crate::declare_thread_stacks_inner!($(#[$attr])* $vis $name, $t, $init);
    );
}

/// The container for the underlying array used to implement the stack
/// of values. Generally you will only ever see this type wrapped
/// inside of `std::thread:LocalKey`, and there is never any reason
/// really to use it directly. Instead use `declare_thread_stacks!`,
/// `let_ref_thread_stack_value!`, `push_thread_stack_value!` and
/// `clone_thread_stack_value`.
pub struct ThreadStack<T> {
    #[doc(hidden)]
    pub inner: UnsafeCell<ThreadStackInner<T>>,
}

impl<T> ThreadStack<T> {
    #[doc(hidden)]
    pub const fn new(initial: T) -> Self {
        ThreadStack {
            inner: UnsafeCell::new(ThreadStackInner::new(initial)),
        }
    }
}

#[doc(hidden)]
pub struct ThreadStackInner<T> {
    data: [MaybeUninit<T>; 64],
    current: usize,
}

#[doc(hidden)]
impl<T> ThreadStackInner<T> {
    pub const fn new(initial: T) -> Self {
        let stack = ThreadStackInner {
            data: [
                // You can't just set the initial value for the whole
                // array to be MaybeUninit::uninit() because that
                // isn't copyable. And you can't use the arr_macro
                // crate because we need the initial value to be
                // explicitly set here rather than overwritten later in
                // order to be a const fn.
                MaybeUninit::new(initial),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
            ],
            current: 0,
        };
        stack
    }
}

#[doc(hidden)]
pub unsafe fn get_thread_stack_value_impl<'a, 'b, T>(
    _hack: &'a (),
    t: &'b ThreadStackInner<T>,
) -> &'a T {
    &*t.data.get_unchecked(t.current).as_ptr()
}

/// Create a local reference to the value at the top of the
/// threadstack. Even though the top value may have been pushed at a
/// much higher layer in the call stack, the reference has a
/// conservative lifetime to guarantee safety -- the same lifetime as
/// a local variable created on the stack where the macro is invoked.
/// If you don't want to have to worry about lifetimes consider using
/// `clone_thread_stack_value` instead.
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
        let $new_variable = s.with(|stack| unsafe {
            $crate::get_thread_stack_value_impl(&stack_lifetime_hack, &*stack.inner.get())
        });
    };
}

#[doc(hidden)]
pub fn compile_time_assert_is_thread_stack<T>(_t: &LocalKey<ThreadStack<T>>) -> () {
    ()
}

#[doc(hidden)]
pub struct ThreadStackGuard<'a, T> {
    stack: *mut ThreadStackInner<T>,
    stack_lifetime_hack: std::marker::PhantomData<&'a ()>,
}

#[doc(hidden)]
pub unsafe fn push_thread_stack_value_impl<'a, 'b, T>(
    _stack_lifetime_hack: &'a (),
    new_value: T,
    t: *mut ThreadStackInner<T>,
) -> ThreadStackGuard<'a, T> {
    (*t).current += 1;
    (*t).data[(*t).current].as_mut_ptr().write(new_value);
    ThreadStackGuard {
        stack: t,
        stack_lifetime_hack: std::marker::PhantomData,
    }
}

impl<'a, T> Drop for ThreadStackGuard<'a, T> {
    fn drop(&mut self) {
        let stack = unsafe { &mut *self.stack };
        let old = unsafe { std::ptr::drop_in_place(stack.data[stack.current].as_mut_ptr()) };
        std::mem::drop(old);
        stack.current -= 1;
    }
}

/// Clone the value currently at the top of threadstack. This lets you
/// avoid worrying about lifetimes but does require a clone to be
/// made.
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
pub fn clone_thread_stack_value<T: Clone>(stack: &'static LocalKey<ThreadStack<T>>) -> T {
    let_ref_thread_stack_value!(the_value, stack);
    the_value.clone()
}

/// Push a new value on the top of the threadstack. this value becomes
/// the value that will be returned by `clone_thread_stack_value` and
/// that `let_ref_thread_stack_value!` will create a reference to. Can
/// only be invoked inside a function, and the effect will last until
/// the end of the current scope. Note that pushing new values will
/// panic if you go beyond the compile time configured maximum
/// threadstack size. The assumption is that threadstacks are mostly
/// used for infrequently set context data, or configuration settings
/// that would otherwise be global variables.
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
        let stack_lifetime_hack = ();
        let s = &$thread_stack;
        $crate::compile_time_assert_is_thread_stack(s);
        let _push_guard = s.with(|stack| unsafe {
            push_thread_stack_value_impl(&stack_lifetime_hack, $new_value, stack.inner.get())
        });
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
}
