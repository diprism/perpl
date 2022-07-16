# The PERPL Language

A PERPL program consists of zero or more definitions and declarations,
followed by an expression.

## Booleans

The only built-in datatype is `Bool`:

    True
    False
    if True then False else True

There is a built-in equality operator (`==`) that returns a `Bool`:

    True == True
    
## Functions and local variables

    \x: Bool. x                          -- with type annotation
    \x. x                                -- without type annotation
    (\x. x) True                         -- application
    (\x. \y. x) True True                -- function of two arguments
    let x = True in x

Lambdas (`\`) must be used _affinely_, that is, no more than once. So
it's an error to write

```
let f = \x . x in (f True, f True)
```

## Products

There are two kinds of tuples, which are accessed in different ways:

    {- Multiplicative product -}
    (True, False, False)                      -- type Bool * Bool * Bool
    let (x, y, z) = (True, False, False) in y -- False
    ()                                        -- type Unit

    {- Additive product -}
    <True, False, False>                      -- type Bool & Bool & Bool
    <True, False, False>.2                    -- False
    <>                                        -- type Top

When you consume a multiplicative product, you consume all
its members:

```
(\x: Bool. x, True)                     -- type (Bool -> Bool) * Bool
let f = \x. x in (f, f)                 -- error: f is used twice
let (f, b) = (\x. x, True) in f b       -- True
```

On the other hand, when you consume an additive product, you consume
just one of its members. Additive products must also be used no more
than once.

```
<\x: Bool. x, True>                     -- type (Bool -> Bool) & Bool
let f = \x. x in <f, f>                 -- type (Bool -> Bool) & (Bool -> Bool)
let f = \x. x in <f, f>.1 True          -- True
let p = <True, True> in (p.1, p.2)      -- error: p is used twice
```

## Datatypes

The type `Bool` is built-in, but its definition would look like this:
```
data Bool =
    False
  | True;
```

Other common simple datatypes:
```
data Unit = unit;                       -- type and ctor can't have the same name

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

Expressions of recursive type must also be affinely used, so it's an error to write

```
data Nat = Zero | Succ Nat;
extern eq: Nat -> Nat -> Bool;
let one = Succ Zero in eq one one;      -- error: one is used twice
```

Infinite (recursive) types are allowed, but the target FGG must have
only finite types. So recursive types need to be eliminated in one of
two ways.

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

## Probabilistic computation

The expression `amb e1 e2` makes a nondeterministic choice between
`e1` and `e2`. That is, the computation splits into two branches, one
in which `e1` is evaluated and one in which `e2` is evaluted. There
can be any number of expressions.

The expression `factor 0.5 in e` multiplies the weight of the current
branch of computation by 0.5 and evaluates `e`.

So to simulate a coin flip, we can write

```
amb (factor 0.5 in True) (factor 0.5 in False)
```

## Global definitions

A global definition looks like this:

    define flip : (Bool -> Unit -> Nat) -> Unit -> Bool -> Nat =
      \ f : Bool -> Unit -> Nat, b : Unit, a : Bool. f a b;
    
Notes:
- The type annotations are all optional.
- The defined symbol (`flip`) must have a type (`(Bool -> Unit -> Nat) -> Unit -> Bool -> Nat`).
- The definition must end with a semicolon (`;`).
- The right-hand side of a definition is usually a lambda expression, but doesn't have to be.

You can use a globally defined symbol any number of times. They are macro-like in the following sense:

    define coin : Bool = amb (factor 0.5 in True) (factor 0.5 in False);
    (coin, coin)

This flips a fair coin twice, that is, four outcomes with probability 0.25 each.

## External declarations

An external declaration looks like this:

    extern flip : (Bool -> Unit -> Nat) -> Unit -> Bool -> Nat;

The target FGG will have a nonterminal symbol `flip` whose rules should be added to it.
