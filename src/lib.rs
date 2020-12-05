//use arr_macro::arr;
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
            $(#[$attr])* $vis static $name: std::cell::UnsafeCell<$crate::ThreadStack<$t>> = std::cell::UnsafeCell::new ($crate::ThreadStack::new($init));
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

pub struct ThreadStack<T> {
    data: [MaybeUninit<T>; 64],
    current: usize,
}

impl<T> ThreadStack<T> {
    pub const fn new(initial: T) -> Self {
        let stack = ThreadStack {
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
    t: &'b ThreadStack<T>,
) -> &'a T {
    &*t.data.get_unchecked(t.current).as_ptr()
}

#[macro_export]
macro_rules! let_ref_thread_stack_value {
    ($new_variable:ident, $thread_stack:expr) => {
        let stack_lifetime_hack = ();
        let $new_variable = $thread_stack.with(|stack| unsafe {
            $crate::get_thread_stack_value_impl(&stack_lifetime_hack, &*stack.get())
        });
    };
}

pub struct ThreadStackGuard<'a, T> {
    stack: *mut ThreadStack<T>,
    stack_lifetime_hack: std::marker::PhantomData<&'a ()>,
}

#[doc(hidden)]
pub unsafe fn push_thread_stack_value_impl<'a, 'b, T>(
    _stack_lifetime_hack: &'a (),
    new_value: T,
    t: *mut ThreadStack<T>,
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

pub fn clone_thread_stack_value<T: Clone>(
    stack: &'static LocalKey<UnsafeCell<ThreadStack<T>>>,
) -> T {
    let_ref_thread_stack_value!(the_value, stack);
    the_value.clone()
}

#[macro_export]
macro_rules! push_thread_stack_value {
    ($new_value:expr, $thread_stack:expr) => {
        let stack_lifetime_hack = ();
        let _push_guard = $thread_stack.with(|stack| unsafe {
            push_thread_stack_value_impl(&stack_lifetime_hack, $new_value, stack.get())
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
