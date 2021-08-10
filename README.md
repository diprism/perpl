# PPL-to-FGG compiler

Compile a PPL file to FGG:
`./compiler.exe < FILE.ppl > OUTPUT.json`

Run tests:
`make tests`

Example: Remove recursive datatypes from code/pda2.ppl
`./compiler.exe --defunctionalize=String --refunctionalize=Stack --linearize=no --compile=no < code/pda2.ppl`



\# | Pipeline Stage            | Description                                     | Flag
--:| ------------------------- | ----------------------------------------------- | -----
 1 | Lex                       | File contents -> list of tokens                 |
 2 | Parse                     | List of tokens -> expressions                   |
 3 | Alpha-rename              | Pick fresh names for all bound variables        | -a
 4 | Type check                | Check file for type errors                      | -t
 5 | Optimize                  | Apply various optimizations                     | -o
 6 | De/refunctionalize        | De/refunctionalize all recursive datatypes      | -d, -r
 7 | Affine-to-linear          | Ensure every function gets called exactly once  | -l
 8 | Optimize (again)          | Apply various optimizations, again              | -o
 9 | Alpha-rename (again)      | Pick fresh names for all bound variables, again | -a
10 | Compile to FGG            | Create FGG rules for all subexpressions         | -c
