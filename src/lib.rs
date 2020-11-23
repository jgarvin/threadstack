#![allow(dead_code)]
#![feature(maybe_uninit_extra)]

use arr_macro::arr;
use std::mem::MaybeUninit;
use std::ops::Deref;

#[macro_export]
macro_rules! declare_thread_stacks {
    // empty (base case for the recursion)
    () => {};

    // process multiple declarations
    ($(#[$attr:meta])* $vis:vis static $name:ident: $t:ty = $init:expr; $($rest:tt)*) => (
        $crate::__declare_thread_stacks_inner!($(#[$attr])* $vis $name, $t, $init);
        $crate::declare_thread_stacks!($($rest)*);
    );

    // handle a single declaration
    ($(#[$attr:meta])* $vis:vis static $name:ident: $t:ty = $init:expr) => (
        $crate::__declare_thread_stacks_inner!($(#[$attr])* $vis $name, $t, $init);
    );
}

// This is done as a separate macro because it is not possible to hide
// a specific macro rules pattern from the documentation.
//
// https://stackoverflow.com/questions/35537758/is-there-a-way-to-hide-a-macro-pattern-from-docs
#[doc(hidden)]
#[macro_export]
macro_rules! declare_thread_stacks_inner {
    ($(#[$attr:meta])* $vis:vis $name:ident, $t:ty, $init:expr) => {
        thread_local! {
            $(#[$attr])* $vis $name: $crate::ThreadStack<$t> = $crate::ThreadStack::new($init);
        }
    }
}

pub struct ThreadStack<T> {
    data: [MaybeUninit<T>; 64],
    current: usize,
}

impl<T> ThreadStack<T> {
    pub fn new(initial: T) -> Self {
        let mut stack = ThreadStack {
            data: arr![MaybeUninit::uninit(); 64],
            current: 0,
        };
        stack.data[0].write(initial);
        stack
    }
}

struct Ref<T> {
    data: *const T,
}

impl<T> Deref for Ref<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.data }
    }
}

#[doc(hidden)]
pub unsafe fn get_parameter_value_impl<'a, 'b, T>(_hack: &'a (), t: &'b ThreadStack<T>) -> &'a T {
    &*t.data.get_unchecked(t.current).as_ptr()
}

#[macro_export]
macro_rules! get_parameter_value {
    ($new_variable:ident, $parameter:expr) => {
        let stack_lifetime_hack = ();
        let $new_variable =
            unsafe { $crate::get_parameter_value_impl(&stack_lifetime_hack, $parameter) };
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let stack = ThreadStack::new(0xDEADBEEFu32);
        get_parameter_value!(stack_value, &stack);
        assert!(stack_value == &0xDEADBEEFu32);
    }
}
