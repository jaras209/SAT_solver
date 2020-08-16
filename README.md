#SAT solver

## formula2cnf

Program which translates a description of a formula in NNF into a DIMACS CNF formula using Tseitin encoding.

The input file contains a description of a single formula in NNF using a very simplified SMT-LIB format following grammatical rules:

`<formula> ::= ('and' <formula> <formula>)
          | ('or' <formula> <formula> )
          | ('not' <variable> )
          | <variable>`
          
Here `<variable>` is a sequence of alphanumeric characters starting with a letter. 
Newline or a sequence of whitespace characters is allowed wherever space is allowed.

The output is a CNF description in the DIMACS format.

Invocation of the program is:

`python formula2cnf.py --input=[input_file] --output=[output_file] --ltr`

Parameters `--input` and `--output` specify the input and output files respectively. 
If they are missing standard input is read or standard output is written to instead.

The program allows an option `--ltr` which specifies if the Tseitin encoding should use only left-to-right implications 
instead of equivalences.

## dpll