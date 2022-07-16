# The PERPL Compiler

PERPL stands for Probabilistic Exact Recursive Programming Language.

## Building the compiler

To build the compiler (requires [GHC](https://www.haskell.org/ghc/)):

    make

To run tests:

    make tests

## Using the compiler
    
To compile a PERPL program to an FGG (JSON-formatted):

    ./perplc [options] FILE.ppl -o OUTPUT.json

For more about the language, see [language.md](language.md).

Options:
        
    -O0 -O1     Optimization level (0 = off, 1 = on)
    -l          Don't linearize the file (implies -c -e)
    -e          Don't eliminate recursive datatypes (implies -c)
    -d DTYPES   Defunctionalize recursive datatypes DTYPES
    -r DTYPES   Refunctionalize recursive datatypes DTYPES
    -c          Compile only to PPL code (not to FGG)
    -z          Compute sum-product
    -o OUTFILE  Output to OUTFILE

## Credits

This code is written by Colin McDonald at the University of Notre Dame
and is licensed under the MIT License.
