A more ergonomic and more flexible form of thread local storage.

[![Docs Status](https://docs.rs/threadstack/badge.svg)](https://docs.rs/threadstack)
[![license](https://img.shields.io/badge/license-MIT-blue.svg)](https://github.com/jgarvin/threadstack/blob/main/LICENCE)
[![crates.io badge](https://img.shields.io/crates/v/threadstack.svg)](https://crates.io/crates/threadstack)

Inspired by the [parameters
feature](https://docs.racket-lang.org/reference/parameters.html)
from Racket.

The general idea is the following. Many applications have
"context" variables that are needed by almost every module in the
application. It is extremely tedious to pass down these values
through every every function in the program. The obvious
temptation is to use a global variable instead, but global
variables have a bunch of widely known downsides:

* They lack thread safety.

* They create a hidden side channel between modules in your
application that can create "spooky action at a distance."

* Because there is only one instance of a global variable modules
in the program can fight over what they want the value of it to
be.

Threadstacks are a middle ground. Essentially instead of having a
global variable, you keep a thread local stack of values. You can only
refer to the value at the top of the stack, and the borrow checker
will guarantee that your reference goes away before the value is
popped. You can push new values on the stack, but they automatically
expire when the lexical scope containing your push ends. Values on the
threadstack are immutable unless you go out of your way to use a type
with interior mutability `Cell` or `RefCell`, so code that wants to
customize the value typically will do so by pushing on onto the stack
rather than clobbering the existing value as would normally occur with
a global variable.

This gives you the effect of a global variable that you can
temporarily override. Functions that before would have referenced
a global variable instead reference the top of the stack, and by
pushing a value on the stack before calling said functions you can
affect their behavior. However you are unable to affect the
behavior when your caller calls those functions because by the
time control returns to your caller the lexical scope containing
your push will have ended and the value you pushed will have
automatically been popped from the stack. This limits the degree
to which different modules can step on each other.

Because the provided `let_ref_thread_stack_value!` creates
references that have a special lifetime tied to the current stack
frame, it is not necessary to wrap all code using thread stack
values inside a call to something like `my_local_key.with(|data|
{...})` like you would have to with the standard `thread_local!`
TLS implementation.



Example:

```
use threadstack::*;

declare_thread_stacks!(
    FOO: String = String::from("hello world");
);

let_ref_thread_stack_value!(my_reference, FOO);
assert!(my_reference == "hello world");

{
    push_thread_stack_value!("hello universe".into(), FOO);
    let_ref_thread_stack_value!(my_other_reference, FOO);
    assert!(my_other_reference == "hello universe");
}

assert!(my_reference == "hello world");
push_thread_stack_value!("hello galaxy".into(), FOO);
assert!(my_reference == "hello world"); // still is reference to old value!
let_ref_thread_stack_value!(my_reference, FOO); // shadows the old reference
assert!(my_reference == "hello galaxy");
````
