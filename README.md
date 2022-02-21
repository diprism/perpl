# PPL-to-FGG compiler

To build the compiler (requires [GHC](https://www.haskell.org/ghc/)):

    make

To compile a PPL file to FGG (JSON-formatted):

    ./compiler.exe FILE.ppl -o OUTPUT.json

To run tests:

    make tests

For more about the language, see [language.md](language.md).

Compilation has the following stages:

\# | Pipeline Stage      | Description                                     | Flag
--:| ------------------- | ----------------------------------------------- | -----
 1 | Lex                 | File contents -> list of tokens                 |
 2 | Parse               | List of tokens -> expressions                   |
 3 | Type check          | Check file for type errors                      |
 4 | Optimize            | Apply various optimizations                     | -O0, -O1
 5 | De/refunctionalize  | De/refunctionalize all recursive datatypes      | -d, -r
 6 | Affine-to-linear    | Ensure every function gets called exactly once  | -l
 7 | Optimize (again)    | Apply various optimizations, again              | -o
 8 | Compile to FGG      | Create FGG rules for all subexpressions         | -c

Command-line invocation:

	./compiler.exe [options] filename.ppl

Options:
        
	-o OUTFILE	Output to OUTFILE
	-O0 -O1		Optimization level (0 = off, 1 = on, for now)
	-c			Compile only to PPL code (not to FGG)
	-l			Don't linearize the file (implies -c)
	-d DTYPES	Defunctionalize recursive datatypes DTYPES
	-r DTYPES	Refunctionalize recursive datatypes DTYPES

## Credits

This code is written by Colin McDonald at the University of Notre Dame and is licensed under the MIT License.