eqil
====

Interpreter and Abstract Interpreter for Coq Intermediate language

These is code from my guest lectures (in progress) in CS252r: Advanced
Functional Language Compilation at Harvard on 10/31, ...

The main files are:

* `semantics.rkt` - semantics of Coq IL
* `abstract-semantics.rkt` - abstract (sound, computable) semantics of Coq IL

To write programs in the Coq IL, use the following:

```
#lang eqil
```

To analyze programs in Coq IL, change that line to the following:

```
#lang eqil/abstract
```

In either case, you can also visualize reduction traces or launch an
algebraic stepper by adding the keyword `traces` or `stepper`, as in:

```
#lang eqil/abstract traces
```
