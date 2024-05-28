# The PERPL Compiler

PERPL stands for Probabilistic Exact Recursive Programming Language. Unlike many general-purpose PPLs, PERPL performs exact inference, via [factor graph grammars](https://github.com/diprism/fggs).
And unlike other PPLs that do support exact inference, PERPL can express unbounded recursive calls and (with some restrictions) recursive data structures.
For example, a PCFG parser written in PERPL appears to generate (infinitely many) trees and sum the probabilities of those (exponentially many) trees that yield a given string; yet it compiles to a cubic-sized system of equations whose solution is equivalent to the CKY algorithm.

For more information:
- Installation: [install.md](install.md)
- Tutorial: [tutorial.md](language.md)
- Language reference: [language.md](language.md)

## Building the compiler

For more detailed instructions, please see [install.md](install.md).

To build the compiler (requires [GHC](https://www.haskell.org/ghc/)):

    make

To run tests:

    make tests

## Using the compiler
    
To compile a PERPL program:

    ./perplc [options] FILE.ppl

Options:
        
    -O0 -O1     Optimization level (0 = off, 1 = on)
    -l          Don't linearize the file (implies -c -e)
    -e          Don't eliminate recursive datatypes (implies -c)
    -d DTYPES   Defunctionalize recursive datatypes DTYPES
    -r DTYPES   Refunctionalize recursive datatypes DTYPES
    -c          Compile only to PPL code (not to FGG)
    -z          Compute sum-product
    -o OUTFILE  Output an FGG to OUTFILE

Although `perplc` can compute sum-products, its implementation is not very efficient. The normal usage is to use the `-o` option to output an FGG to a JSON file. Then the FGG can be processed using [the `fggs` package](https://github.com/diprism/fggs).

## Credits

This code is written by Colin McDonald (University of Notre Dame) with contributions from David Chiang (University of Notre Dame) and Chung-chieh Shan (Indiana University) and is licensed under the MIT License. It is based upon work supported by the National Science Foundation under Award Nos. CCF-2019266 and CCF-2019291.
