# The PERPL Language

A PERPL program consists of zero or more definitions, followed by an
expression.

## Booleans

The only built-in datatype is `Bool`:

    True
    False
    if True then False else True

There is a built-in equality operator (`==`) that returns a `Bool`:

    True == True
    
## Functions and local variables

PERPL has first-class functions (lambda-expressions):

    \x: Bool. x                          -- with type annotation
    \x. x                                -- without type annotation
    (\x. x) True                         -- application
    (\x. \y. x) True True                -- function of two arguments

Let-binding:

    let x = True in x
    
However, lambda expressions are one of several types of expressions that must be used _affinely_, that is, no more than once. So it's an error to write

```
let f = \x . x in (f True, f True)
```
    
## Products

There are two kinds of tuples, which are accessed in different ways. _Multiplicative_ tuples 

    (True, False, False)                      -- type (Bool, Bool, Bool)
    ()                                        -- type ()
    let (x, y, z) = (True, False, False) in y -- False

When you consume a multiplicative tuple, you consume all
its members:

    let f = \x. x in (f, f)                   -- error: f is used twice

The other kind of tuple is called _additive_. 

    <True, False, False>                      -- type <Bool, Bool, Bool>
    <>                                        -- type <>
    let <_, y, _> = <True, False, False> in y -- False

When you consume an additive tuple, you consume just one of its
members. So in a `let <...> = ...` expression, the left-hand side must
have exactly one variable; the other positions must be `_`.

    let <x, y, z> = <True, False, False> in y -- error

Additive products must be used affinely (no more than once).

    let f = \x. x in <f, f>                   -- not an error

## Datatypes

The type `Bool` is built-in, but its definition would look like this:

    data Bool =
        False
      | True;

Note that datatype definitions are terminated with a semicolon.

Other common datatypes:

    data Maybe a =
        Nothing
      | Just a;
    
    data Either a b =
        Left a
      | Right b;

Recursive datatypes are allowed:

    data Nat =
        Zero
      | Succ Nat;
      
    data List a =
        Nil
      | Cons a List;

Mutually-recursive datatypes are allowed too:

    data Tree =
        Leaf
      | Node Children;
    
    data Children =
        Nil
      | Cons Tree Children;

Expressions of recursive type must be used affinely (no more than
once), so it's an error to write

    data Nat = Zero | Succ Nat;
    let one = Succ Zero in (one, one);      -- error: one is used twice

Although recursive types, which have an infinite number of
inhabitants, are allowed, the target FGG can only have types with a
finite number of inhabitants. So recursive types need to be eliminated
in one of two ways.

Let `A` be a recursive datatype.

- `A` can be _defunctionalized_ if, for every constructor `Con` of
  `A`, no expression `Con e` has a free variable whose type
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
in which `e1` is evaluated and one in which `e2` is evaluated. `amb`
can take any number of expressions.

The expression `factor 0.5 in e` multiplies the weight of the current
branch of computation by 0.5 and evaluates `e`. The expression `fail`
(which can optionally be annotated with a type, like `fail: Bool`)
multiplies the weight of the current branch by 0.

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
- The definition must end with a semicolon (`;`).
- The right-hand side of a definition is usually a lambda expression, but doesn't have to be.

You can use a globally defined symbol any number of times. They are lazily evaluated, as the following example illustrates:

    define coin = amb (factor 0.5 in True) (factor 0.5 in False);
    (coin, coin)

Both calls to `coin` flip a coin, that is, so that there are four outcomes with probability 0.25 each.

## External declarations

An external declaration looks like this:

    extern flip : (Bool -> Unit -> Nat) -> Unit -> Bool -> Nat;

The target FGG will have a nonterminal symbol `flip` whose rules should be added to it.
