**Rampart Language Guide**

**Note**

This document is a work in progress. Neither the language nor this guide is complete. At the moment the compiler implements a lexer, parser, and symbol-binding pass for a small subset of the language. An abstract syntax tree (AST) is available. As written, this document is primarily a language design specification and should evolve into a full language guide.

It is acceptable for the compiler to contain features that are not yet documented here, and for this document to describe features that the compiler does not yet implement.

The compiler back-end will be LLVM, which has e.g. escapement analyisis and other optimization capabilities.

**Language overview**
- Statically typed
- Automatic memory management via reference counting
- Memory safe
  - Memory leaks are considered memory-safe, including those caused by cycles
  - Undefined behavior is constrained (TODO: define UB) so as not to undermine memory safety
- C-like syntax
- Statements are delimited with `;` or by newlines

**Types**
- Integer (`int`)
- Boolean (`bool`)
- Type (`type`)
- Tuple
  - `void` identifies the 0-tuple type
- Struct
- Variant
- Fixed array
- Dynamic array (size can change at runtime)
- Function

Types are first-class values: they are expressions, may be stored in variables, passed as arguments, and returned from functions.

```
let t = int        // `t` is a variable whose value is the type `int`
t x                // `t` is a compile-time constant, so this declares a variable `x` of type `int`

type optional(type t) const {
    return None | Some t        // type composition resulting in a variant type
}
optional(int) i = Some 7
```

Declaration types must be compile-time constants. This ensures the compiler can reduce programs to a sound type system suitable for conventional static type checking.

Types are structural rather than nominal:
```
optional(int) i
optional(int) j                 // 'i' and 'j' have the same type
```

Types are first-class at runtime as well and may be used for reflection. To remain compatible with ahead-of-time compilation, some restrictions apply: for example, it is not permitted to create a new type at runtime and then instantiate it.

**Variables**

Variables are immutable by default. Use the `mut` keyword to declare a mutable variable.

```
int x = 0     // `x` is immutable
mut int y     // `y` is mutable

x = 1         // ERROR: `x` is immutable
y = 1         // OK: `y` is mutable
```

Mutable variables do not require an initializer if their type has a default value. Immutable variables must have an initializer expression. If the initializer is a compile-time constant, the immutable variable is itself a compile-time constant.

Immutable variables can also be declared using `let`. In that form the type is deduced from the initializer. When a `let` appears in statement position, it adds the variable to the surrounding environment just like a declaration.

```
let x = 0     // `x` is an immutable `int`
```

`let` expressions may be paired with `in` to declare variables scoped to a sub-expression.

```
let y = let x = 1 in x + 1
// `x` is not in scope here but `y` is
```

**Functions**

Functions have many first-class characteristics, but with restrictions designed to avoid implicit dynamic allocation of closures.

There are two syntaxes for defining functions: a C-like syntax and a lambda-expression syntax. The lambda syntax may optionally deduce the return type.

```
void c_like_syntax(int a, bool b) {
}

let lambda_syntax = void&(int a, bool b) {
}

let with_return_type_deduction = &(int a, int b) -> a + b
```

A nested function may capture variables from its enclosing scopes.

```
void f(int a, int b) {
  int sum() { return a + b }  // OK: captures `a` and `b`
}
```

A function may be passed as an argument to another function.

```
int g(int<-int op) {
  return op(3)
}

int f(int a) {
  int sum(int b) {
    return a + b  // OK: captures `a`
  }
  return g(sum)   // OK: `sum` is passed as an argument
}
```

A function value may be stored in a local variable.

```
int f(int a, int b) {
  mut (int<-void) op = &() -> 0
  op = &() -> a + b        // OK: `op` is a local variable
  return op()
}
```

By default, values that refer to local variables may not be returned or stored outside the local frame, since that could allow a function to outlive its closure.

```
mut int<-(int,int) op = &(int, int) -> 0

int<-(int,int) f(int c) {
  int sum(int a, int b) { return a + b + c }   // OK: captures `c`
  op = sum                                     // ERROR: `op` is global, cannot store this closure
  return sum                                   // ERROR: cannot return this closure
}
```

By contrast, a free function may be returned or stored without restriction. A free function in truly first class. Its closure is dynamically allocated. Mutable variables captured by free functions are boxed. The 'free' keyword makes the dynamic allocation explicit. The freeness of a function is _not_ considered part of its type.

Runtime checks ensure non-free functions never escape. The freeness of a function is stored within the closure to ensure runtime checks are fast. Additionally, the compiler performs escapement analysis and other methods to eliminate runtime checks where freeness can be statically determined.

```
mut int<-(int,int) op = &(int, int) free -> 0       // 'free' keyword appears in lambda expression but not type
int c2 = 0;
int<-(int,int) f(int c) {
  int sum(int a, int b) free { return a + b + c }   // OK: 'c' is copied into the dynamically allocated closure
  op = sum                                          // OK: `sum` is free
  return sum                                        // OK
}
```

If a function only accesses local and global variables, it does not need a closure. In this case it is associated with the empty closure. Such a function is considered free whether or not the 'free' keyword is applied.

```
mut int<-(int,int) op = &(int, int) -> 0
int c = 0;
int<-(int,int) f() {
  int sum(int a, int b) { return a + b + c }      // OK: 'c' is implicitly free because its closure is empty
  op = sum                                        // OK: 'sum' is implicitly free
  return sum                                      // OK
}
```

A pure function may only access captured variables when they are immutable. It may only modify mutable variables in the local frame and may only call pure or const functions. Pure functions may be implicitly converted to impure.

A const function is more restricted than pure: it may only access captured variables that are compile-time constants and it may only call other const functions. Const functions may be implicitly converted to pure or impure functions. Only const functions may be evaluated at compile time, and then only in specific grammatical contexts; const functions may also be evaluated at runtime.

The following shows a const function used in a declaration type; the call is evaluated at compile time.

```
type f() const { return int }
f() x   // OK: `x` has type `int`
```

Const functions may also be invoked at compile time in other contexts when the call expression itself is const-qualified.

```
int fib (int n) const {
  return n <= 2 ? 1 : fib(n-1) + fib(n-2)
}
let x = fib(3)            // `x` is immutable and has value 2; `fib` is not evaluated at compile time here
let y = fib(3) const      // `y` is a compile-time constant with value 2
```

A count of iterations, including iterations by recursion, ensures hangs cannot occur at compile time. The count is reset to zero whenever an outermost const function evaluation completes.

**TODO**
- Arity
- Typeof
- Arithmetic
- Control flow, including pattern matching
- ...