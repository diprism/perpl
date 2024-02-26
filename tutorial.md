# PERPL Tutorial
PERPL is a probabilistic programming language developed specifically to address recursive problems with precise solutions. Unlike traditional approaches that generate random outcomes, this language thoroughly examines the possibilities of outcomes and calculates the distribution of results accurately. By using this method, recursive problems can be solved in polynomial time, offering significant efficiency and accuracy improvements over conventional methods.

## Windows system instructions: 

Download WSL (Windows Subsystem for Linux)  

Check which version of python3 you have: (otherwise, install python3) 

    python3 --version 

Install Git: 

    sudo apt-get install git install

Install GHC: 

    sudo apt install ghc

## Clone the /fggs repository from Github:

    git clone https://github.com/diprism/fggs.git
    pip install -r requirements.txt
> Note: It may take a while because there are many files to download

## To build the compiler:
Go to the perpl/ directory:

    cd path/to/perpl

To build the compiler (requires GHC):

    make

To run tests:

    make tests

## To compile a PERPL program:

    ./perplc [options] FILE.ppl

**The -z and -o flags:**

To compute the sum product: use `-z` flag

    ./perplc -z ./examples/von_neumann.ppl

 To output an FGG: use `-o` flag and indicate an outfile

    ./perplc -o stairs.fgg ./examples/stairs.ppl

## To compute the sum product using the FGG output:

Go to the fggs/ directory, then access the FGG file from the perpl/ directory to calculate sum product. 

    cd path/to/fggs
    PYTHONPATH=.:$PYTHONPATH python3 bin/sum_product.py ~/perpl/stairs.fgg

# Non-probabilistic Features:
## Booleans: False, True, if
The only built-in datatype is  `Bool`:
```
True
True == not False
```
```
False
False == not True
```
```
if
if True then False else True
```

There is a built-in equality operator (`==`) that returns a  `Bool`:
```
True == True
if x==y then True else False  -- True if x is equal to y, otherwise False
```

## let
Let-binding:
```
let x = True in x
```
```
let x = 5 -- Define a variable x with value 5 
let y = 7 -- Define a variable y with value 7 
let z = x + y -- Define a variable z with the sum of x and y
-- z is now 5 + 7, which is 12
```

## Functions: define, recursion

PERPL has first-class functions (lambda-expressions):
```
\x: Bool. x                          -- with type annotation
\x. x                                -- without type annotation
(\x. x) True                         -- application
(\x. \y. x) True True                -- function of two arguments
```
Example: Verify DeMorgan's Laws: 
```
define and = \ a. \ b. if a then b else False;
define or = \ a. \ b. if a then True else b;
define not = \ a. if a then False else True;
define xor = \ a. \ b. if a then not b else b;
define flip = amb True False;  -- either True or False

let a = flip in
let b = flip in
(not (and a b) == or (not a) (not b), not (or a b) == and (not a) (not b))
```

However, lambda expressions are one of several types of expressions that must be used  _affinely_, that is, no more than once. So it's an error to write
```
let f = \x . x in (f True, f True)   -- error: f used twice
```

## Multiplicative tuples: 
Tuples are often used to represent fixed-size collections of heterogeneous data, such as `(Int, Bool, String)`. Tuples are immutable, meaning that once they are created, their elements cannot be modified.

There are two kinds of tuples, which are accessed in different ways.  _Multiplicative_  tuples are the same as tuples in many other languages:
```
(True, False, False)                      -- type (Bool, Bool, Bool)
()                                        -- type ()
let (x, y, z) = (True, False, False) in y -- False
```

When you consume a multiplicative tuple, you consume all its members using `let`: 
```
let f = \x. x in (f, f)                   -- error: f is used twice
```

## datatypes: data, case, recursive types
The type  `Bool`  is built-in, but its definition would look like this:
```
data Bool =
    False
  | True;
```
> Note: datatype definitions are terminated with a semicolon.

Other common datatypes:
```
data Maybe a =
    Nothing
  | Just a;

data Either a b =
    Left a
  | Right b;
```
Recursive datatypes are allowed:
```
data Nat =
    Zero
  | Succ Nat;
  
data List a =
    Nil
  | Cons a List;
```
Mutually-recursive datatypes are allowed too:
```
data Tree =
    Leaf
  | Node Children;

data Children =
    Nil
  | Cons Tree Children;
```
Expressions of recursive type must be used affinely (no more than once), so it's an error to write
```
data Nat = Zero | Succ Nat;
let one = Succ Zero in (one, one);      -- error: one is used twice
```


