# PPL-to-FGG compiler

## Usage

Building the compiler requires [GHC](https://www.haskell.org/ghc/):
`make`

Compile a PPL file to FGG (JSON-formatted):
`./compiler.exe < FILE.ppl > OUTPUT.json`

Run tests:
`make tests`

## Expressions

The basic syntax is mostly Haskell-like. These are all expressions:

Booleans:

    True
    False
    if True then False else True
    
Functions:

    \x: Bool. x                       -- the variable must be annotated with a type
    (\x: Bool. x) True                -- application
    (\x: Bool. \y: Bool. x) True True -- function of two arguments
    (\x: Bool, y: Bool. x)  True True -- another way of writing the same thing

Let:

    let x = True in x

There are two kinds of tuples, which are accessed in different ways:

    {- Multiplicative product -}
    (True, False, False)                      -- type Bool * Bool * Bool
    let (x, y, z) = (True, False, False) in y

    {- Additive product -}
    <True, False, False>                      -- type Bool & Bool & Bool
    <True, False, False>.2

## Affine types

Lambdas (`\`) must be used _affinely_, that is, no more than once. So
it's an error to write

```
let f: Bool -> Bool = \x: Bool . x in (f True, f True)
```

or

```
data Nat = Zero | Succ Nat;
extern eq: Nat -> Nat -> Bool;
let one = Succ Zero in eq one one; -- error: one is used twice
```

This is why we have two kinds of products, multiplicative and
additive. When you consume a multiplicative product, you consume all
its members:

```
(\x: Bool. x, True)                     -- type (Bool -> Bool) * Bool
let f = \x: Bool. x in (f, f)           -- error: f is used twice
let (f, b) = (\x: Bool. x, True) in f b -- True
```

On the other hand, when you consume an additive product, you consume
just one of its members. Additive products must also be used no more
than once.

```
<\x: Bool. x, True>                    -- type (Bool -> Bool) & Bool
let f = \x: Bool. x in <f, f>          -- type (Bool -> Bool) & (Bool -> Bool)
let f = \x: Bool. x in <f, f>.1 True   -- True
let p = <True, True> in (p.1, p.2)     -- error: p is used twice
```

## Programs

A program consists of zero or more definitions and declarations, followed by an expression.

### Global definitions

A global definition looks like this:

    define flip : (Bool -> Unit -> Nat) -> Unit -> Bool -> Nat =
      \ f : Bool -> Unit -> Nat, b : Unit, a : Bool. f a b;
    
Notes:
- The defined symbol (`flip`) must have a type (`(Bool -> Unit -> Nat) -> Unit -> Bool -> Nat`).
- The definition must end with a semicolon (`;`).
- The right-hand side of a definition is usually a lambda expression, but doesn't have to be.

You can use a globally defined symbol any number of times. They are macro-like in the following sense:

    define coin : Bool = (sample uniform : Bool);
    (coin, coin)

This flips a fair coin twice, that is, four outcomes with probability 0.25 each.

### External declarations

An external declaration looks like this:

    extern flip : (Bool -> Unit -> Nat) -> Unit -> Bool -> Nat;

The target FGG will have a nonterminal symbol `flip` whose rules should be added to it.

### Datatype declarations

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

Expressions of recursive type must also be affinely used.

## Probabilistic computation

A `sample` expression nondeterministically samples from a distribution
(which might or might not sum to one). There are three built-in
distributions you can sample from: `uniform` (every outcome gets equal
probability, summing to one), `amb` (every outcome gets a weight of
one), and `fail` (every outcome gets a weight of zero).

```
sample uniform : Bool -- True : 0.5, False : 0.5
sample amb : Bool     -- True : 1,   False : 1
sample fail : Bool    -- True : 0,   False : 0
```

An external definition might also be probabilistic.

## De-/Refunctionalization

Our language allows infinite (recursive) types, but the target FGG
must have only finite types. So recursive types need to be eliminated
in one of two ways.

Let `A` be a recursive datatype.

- `A` can be _defunctionalized_ if, for every constructor `Con` of
  `A`, no expression `Con e` has a free variable whose types
  contains `A`.

- `A` can be _refunctionalized_ if for every expression `case e of
  ...` where `e` is of type `A`, the type of the case-of expression
  does not contain `A`, and the free variables in each case `Con x1
  ... xn -> e'` have types that do not contain `A`. Note that the
  variables `x1 ... xn` are not considered free here, so their types
  _can_ contain `A`.

In order to compile, each recursive datatype must satisfy at least one
of the two conditions above.

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
