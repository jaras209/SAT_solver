# CDCL SAT solver
This project is the implementation of the CDCL SAT solver. The final and most powerful version is the `cdcl_heuristic.py`

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
## dpll_wl
Adds watched literals data structure to the DPLL solver.

The invocation of the program is:

`python dpll3_wl.py [input_file]`

* Parameter `[input_file]` specifies the input file. The format of the input file is detected by the extension ('.cnf' for DIMACS, '.sat' for the simplified SMT-LIB format).

## cdcl
CDCL solver which adds clause learning and restarts to the DPLL solver (with watched literals).

Clause learning stops at the first UIP.

Clause deletion uses LBD and everytime the restart occurs, the learned clauses with LBD greater than a limit are removed. This limit increases geometrically by a factor of 1.1.

Restarts occur when the number of conflicts reaches some limit. This limit increases geometrically by a factor of 1.1.

The program is able to read two input formats:
1. The simplified SMT-LIB format described in formula2cnf.
2. The DIMACS format, also described in the formula2cnf.

The solver outputs whether the formula is satisfiable (SAT) or unsatisfiable (UNSAT). In case of a satisfiable formula a model is a part of the output as well. The model is printed as a set of literals.

Statistical information is part of the output as well:
* Total CPU time
* Number of decisions
* Number of steps of unit propagation (i.e. how many values were derived by unit propagation)
* Number of restarts

The invocation of the program is:

`python cdcl.py [input_file] --conflicts_limit --lbd_limit`

* Parameter `[input_file]` specifies the input file. The format of the input file is detected by the extension ('.cnf' for DIMACS, '.sat' for the simplified SMT-LIB format). 

 * `--conflicts_limit` is the initial limit on the number of conflicts before the CDCL solver restarts. 
 * `--lbd_limit` is the initial limit on the number of different decision levels in the learned clause for clause deletion.
 
 ## cdcl_heuristic
Adds two decision heuristics (and random) for choice of branching literal and also assumptions to the previous version of the CDCL solver.

The used heuristics are:
* Finds the unassigned literal which occurs in the largest number of not satisfied clauses.
* Finds the unassigned literal based on VSIDS heuristic, i.e. the literal which is present the most in the learned clauses.
* Finds the unassigned literal at random.

The assumption is a list of literals which represents an assumption about the initial values of specified variables.

The invocation of the program is:

`python cdcl.py [input_file] --assumption --heuristic --conflicts_limit --lbd_limit`

* `[input_file]` specifies the input file. The format of the input file is detected by the extension ('.cnf' for DIMACS, '.sat' for the simplified SMT-LIB format). 
* `--assumption` is a space separated sequence of integers representing assumption about initial values of specified variables. For example: `--assumption 1 -2 3`. Default is an empty sequence.
* `--heuristic` specifies a decision heuristic: 
    * `0` - pick the unassigned literal which occurs in the largest number of not satisfied clauses 
    * `1` - pick the unassigned literal based on VSIDS heuristic (default value)
    * `2` - pick the random unassigned literal
* `--conflicts_limit` is the initial limit on the number of conflicts before the CDCL solver restarts. Default value is set to 100.
* `--lbd_limit` is the initial limit on the number of different decision levels in the learned clause for clause deletion. Default value is set to 3.

## backbones
A program which uses a CDCL SAT solver as an oracle and finds all backbones of a given CNF formula.

It uses a priority queue (min heap) to minimize the number of SAT calls. The priority of the literal is its number of occurrences in the clauses of the formula multiplied by -1.

The invocation of the program is:

`python backbones.py [input_file]`

* `[input_file]` specifies the input file. The format of the input file needs to be `.cnf` for DIMACS formula.

Program outputs the list of backbone literals, if any, and also the number of SAT solver calls and the total CPU time of the computation.
