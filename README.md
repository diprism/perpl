# PPL-to-FGG compiler

Compile a PPL file to FGG (JSON-formatted):
`./compiler.exe < FILE.ppl > OUTPUT.json`

Run tests:
`make tests`

Example: Remove recursive datatypes from code/pda2.ppl
`./compiler.exe --linearize=no --compile=no < code/pda2.ppl`

## Syntax

A program consists of zero or more definitions and declarations, followed by an expression.

### Global Definitions

A global definition looks like this:

    define flip : (Bool -> Unit -> Nat) -> Unit -> Bool -> Nat =
      \ f : Bool -> Unit -> Nat, b : Unit, a : Bool. f a b;
    

Notes:
- The defined symbol (`flip`) must have a type (`(Bool -> Unit -> Nat) -> Unit -> Bool -> Nat`).
- The argument of a lambda expression (`\ f`) must also have a type.
- The definition must end with a semicolon (`;`).
- The right-hand side of a definition is usually a lambda expression, but doesn't have to be.

You can use a globally defined symbol any number of times. They are macro-like in the following sense:

    define coin : Bool = (sample uniform : Bool);
    (coin, coin)

This flips a fair coin twice, that is, four outcomes with probability 0.25 each.

### External Declarations

An external declaration looks like this:

    extern flip : (Bool -> Unit -> Nat) -> Unit -> Bool -> Nat;

The target FGG will have a nonterminal symbol `flip` whose rules should be added to it.

### Datatype Declarations

The type `Bool` is built-in, but its definition would look like this:
```
data Bool =
    False
  | True;
```

Other common simple datatypes:
```
data Unit = unit; -- type and ctor can't have the same name

data List =
    Nil
  | Cons Bool List;
```

Mutually recursive datatypes are allowed too:
```
data Tree =
    Leaf
  | Node Children;

data Children =
    Nil
  | Cons Tree Children;
```

### Expressions

Lambdas (`\`), additive products (`<...>`), and recursive types must
be used _affinely_, that is, no more than once.

## De-/Refunctionalization

Let `M` be a recursive datatype. Then
- We can _defunctionalize_ `M` when, for each `M` constructor occurrence, the types of the args it is instantiated with do not depend on `M`.
- We can _refunctionalize_ `M` when, for each `M` case-of, neither the return type nor the types of the free vars in each case depend on `M`. Note that you _can_ use the constructor args you are given in each case even if their types depend on `M`.

In order to compile, each recursive datatype must satisfy at least one of the two conditions above.

## Compilation Stages

\# | Pipeline Stage            | Description                                     | Flag
--:| ------------------------- | ----------------------------------------------- | -----
 1 | Lex                       | File contents -> list of tokens                 |
 2 | Parse                     | List of tokens -> expressions                   |
 3 | Type check                | Check file for type errors                      | -t
 4 | Optimize                  | Apply various optimizations                     | -o
 5 | De/refunctionalize        | De/refunctionalize all recursive datatypes      | -d, -r
 6 | Affine-to-linear          | Ensure every function gets called exactly once  | -l
 7 | Optimize (again)          | Apply various optimizations, again              | -o
 8 | Compile to FGG            | Create FGG rules for all subexpressions         | -c
