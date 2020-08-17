# SAT solver

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
DPLL solver which implements the basic branch and bound DPLL algorithm with unit propagation.

The program is able to read two input formats:
1. The simplified SMT-LIB format described in formula2cnf.
2. The DIMACS format, also described in the formula2cnf.

The solver outputs whether the formula is satisfiable (SAT) or unsatisfiable (UNSAT). In case of a satisfiable formula a model is a part of the output as well. The model is printed as a set of literals.

Statistical information is part of the output as well:
* Total CPU time
* Number of decisions
* Number of steps of unit propagation (i.e. how many values were derived by unit propagation)

The invocation of the program is:

`python dpll.py --input=[input_file]`

Parameter `--input` specifies the input file. The format of the input file is detected by the extension ('.cnf' for DIMACS, '.sat' for the simplified SMT-LIB format).
