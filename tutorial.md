# PERPL Tutorial

PERPL is a probabilistic programming language developed specifically to address recursive problems with precise solutions. Unlike traditional approaches that generate random outcomes, this language thoroughly examines the possibilities of outcomes and calculates the distribution of results accurately. By using this method, recursive problems can be solved in polynomial time, offering significant efficiency and accuracy improvements over conventional methods.

## To compile a PERPL program:

    ./perplc [options] FILE.ppl

**The -z and -o flags:**

To compute the sum product: use `-z` flag

    ./perplc -z ./examples/von_neumann.ppl

 To output an FGG: use `-o` flag and indicate an outfile

    ./perplc -o stairs.fgg ./examples/stairs.ppl

## To compute the sum product using the FGG output:

    PYTHONPATH=../fggs:$PYTHONPATH python3 ../bin/sum_product.py stairs.fgg

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
# Probabilistic Features
## amb 
`amb` splits the program into different branches to separately calculate the results of each possible scenario. 
Mention how the program is 

    amb (Zero) (Succ Zero) (Succ(Succ Zero))
The program splits into three branches, shown below. Each branch gets evaluated separately. 

    ┌────────► Zero                                                                                  
    │                                                    
    ├────────► Succ Zero ─────► 1                                                                    
    │                                                    
    └────────► Succ(Succ Zero) ─────► Succ 1 ─────► 2

Example: 
Suppose you flip two fair coins, with 0.5 chance in both heads and tails. 

    define flip = amb (factor 0.5 in H) (factor 0.5 in T) 
                                                0.5            
                        0.5               ┌──────► H H     
                     ┌───────► (H, flip) ─┤                
                     │                    └──────► H T     
                     │                      0.5            
    (flip, flip)─────┤                                     
                     │                      0.5            
                     │                    ┌──────► T H     
                     └───────► (T, flip) ─┤                
                        0.5               └──────► T T     
                                            0.5            
                                                      

## Factor
Factor f: multiply the current branch by f. Higher weight on the branch means higher possibility of that branch's outcome. The factors in the end should all add up to 1. 
Factor 0: fail. The branch with factor 0 has no weight in the final result, or in other words, the branch ends. 

Example: stairs.ppl

    {- https://leetcode.com/problems/climbing-stairs/
       You are climbing a staircase. It takes n steps to reach the top.        
       Each time you can either climb 1 or 2 steps. In how many distinct ways can you climb to the top? -}
    
    data Nat = Zero | Succ Nat; 
    
    define climb = \stairs.
      case stairs of
      | Zero -> ()
      | Succ stairs -> 
        amb (climb stairs)   -- take one step
            (case stairs of  -- take two steps
             | Zero -> fail
             | Succ stairs -> climb stairs);
    
    climb (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))) -- Should return the (n+1)'st Fibonacci number (21)
    
    -- correct: [21.0]

Example: von_neumann.ppl, an example with different factors. 

    {- Von Neumann's trick for simulating a fair coin with an unfair one:
       flip the unfair coin twice. If the result is HT, treat it as H; if
       the result is TH, treat it as T. Otherwise, repeat.
    
       You need to supply the probability of H and T as the factor `unfair`.
    
       You can compute the gradient of H with respect to the unfair
       probabilities and verify that they are equal, showing that the
       output distribution remains fair in a neighborhood of the given
       unfair distribution.
    
       https://en.wikipedia.org/wiki/Fair_coin#Fair_results_from_a_biased_coin -}
    
    data Flip = H | T;
    define unfair = amb (factor 0.6 in H) (factor 0.4 in T);    
    
    define fair =
      let c1 = unfair in
        let c2 = unfair in
          if c1 == c2 then fair else c1;
    
    fair


## Linearity

Linear variables are local variables that has to be used strictly once. 

    let x = Succ Zero in false --allowed under affine types, not allowed under strictly linear types
    let x = Succ Zero in x --allowed
    let x = Succ Zero in (x, x) --not allowed to use twice
    define fair = (x, x) --also not allowed because recursive datatypes are linear
    
PERPL uses affine types, slightly different from strictly linear types. The complier changes the affine types to linear types internally. PERPL has this restriction because it is supposed to run in polynomial time. 

Linearity is similar to reading a file in Python, where you can't read .txt files twice. Another way to think about it is having two pointers pointing to the same thing, which could cause errors. 

### Positive and Non-Positive Types
|  | positive (non-recursive data) | non-positive(recursive data) |
|--|--|--|
| local | can copy | cannot copy |
| global| can copy | cannot copy |

Every type consists of the type itself and the type constructor: 
|Type| Constructor |
|--|--|
| Bool | True, False |
| ->| \x. (lambda) expressions |
| &| Additive tuples < , > |
| *| Multiplicative tuples ( , ) |

PERPL does have types, similar to Haskell, but the PERPL compiler automatically figures out the types, so writing the types while you write a PERPL program is optional. 

## Defunctionalization/Refunctionalization
PERPL cannot have infinite types (like Nat, where there are infinite amount of natural numbers), so one way PERPL eliminates infinite types is through Defunctionalization/refunctionalization. 
### Defunctionalization
Here we have a program that determines if a number is odd or even. 

    data Nat = Zero | Succ Nat; 
    define even (n: Nat) = 
	    case n if 
		    Zero -> True
		    | Succ m -> not (even m); 
	even (Succ(Succ Zero)) --returns even

Defunctionalization delays constructors (Succ and Zero here) and uses placeholders in place until the final calculation step. 

### Refunctionalization
Here we have a program that compares two colors: True if the two colors are the same, else False. 

    data Nat = Zero | Succ Nat; 
    data Color = Red | Green | Blue; 
    data List = Nil | Cons Nat List; 
    define mem x l =  -- x is member of l
	    case l of 
			| Nil -> False
			| Cons first rest -> 
				if first = x then True -- x is free variable
				else mem x rest -- recursion step
	
	let l = Cons Red (Cons Blue Nil) in mem Red l; 
 

In refunctionalization, types of free variables become target of the arrows in the graphs (shown below). Refunctionalization calculates constructors early before the function call so that the recursion would be eliminated. 

The compiler choses whether to use D or R in the process. 
The graphs below demonstrate the process of PERPL de/refunctionlizing a program: D represents defunctionalization, R represents refunctionalization. In the end the program becomes a non-recursive types. Every node should choose D or R, and no cycles are allowed in the graph. 

            D                    
        ────────►                
      A           B              
        ◄────────                
      │     D     │              
    R │           │ R            
      │           │              
      ▼           ▼              
      C ────────► ∅              
           D,R                   
                                 
            │                    
            │                    
            │ Defunctionalize B  
            │                    
            ▼                    
            D                 
      A ──────────┐              
                  │              
      │           │              
    R │           │              
      │           │              
      ▼           ▼              
      C ────────► ∅              
           D,R                   
                                 
            │                    
            │                    
            │ Defunctionalize A  
            │                    
            ▼                    
                                 
      C ────────► ∅              
           D,R                   
                                 
            │                    
            │                    
            │ Defunctionalize C  
            │                    
            ▼                                      
            ∅                    
                                 
An example of an unacceptable graph with cycles: In this case, the program will never become an non-recursive type. 

                R                 
     ┌──┐   ────────►   ┌──┐      
    D│  ▼ A           B ▼  │R     
     └──┘   ◄────────   └──┘      
                R                 
 
