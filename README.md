# PPL-to-FGG compiler

Compile a PPL file to FGG (JSON-formatted):
`./compiler.exe < FILE.ppl > OUTPUT.json`

Run tests:
`make tests`

Example: Remove recursive datatypes from code/pda2.ppl
`./compiler.exe --linearize=no --compile=no < code/pda2.ppl`

## Syntax

### Function Definitions

TODO: way more documentation
```
define flip : (Bool -> Unit -> Nat) -> Unit -> Bool -> Nat =
  \ f : Bool -> Unit -> Nat, b : Unit, a : Bool. f a b;
```

### Datatype Declarations

```
data Bool =
    False
  | True;

data List =
    Nil
  | Cons Bool List;
```



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
