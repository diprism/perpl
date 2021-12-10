# PPL-to-FGG compiler

To build the compiler (requires [GHC](https://www.haskell.org/ghc/)):

    make

To compile a PPL file to FGG (JSON-formatted):

    ./compiler.exe < FILE.ppl > OUTPUT.json

To run tests:

    make tests

For more about the language, see [language.md](language.md).

Compilation has the following stages:

\# | Pipeline Stage      | Description                                     | Flag
--:| ------------------- | ----------------------------------------------- | -----
 1 | Lex                 | File contents -> list of tokens                 |
 2 | Parse               | List of tokens -> expressions                   |
 3 | Type check          | Check file for type errors                      |
 4 | Optimize            | Apply various optimizations                     | -o
 5 | De/refunctionalize  | De/refunctionalize all recursive datatypes      | -d, -r
 6 | Affine-to-linear    | Ensure every function gets called exactly once  | -l
 7 | Optimize (again)    | Apply various optimizations, again              | -o
 8 | Compile to FGG      | Create FGG rules for all subexpressions         | -c

The `-o`, `-l`, and `-c` options are followed by either `Y` or `N` and
turn the corresponding stage on or off.

The `-d` and `-r` options are followed by a type name and force
defunctionalization or refunctionalization (respectively) for that
type.
