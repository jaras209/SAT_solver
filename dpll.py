import argparse
from formula2cnf import formula2cnf
import time
from typing import Tuple, Optional, Iterable
from collections import deque

'''
====================================== dpll3 ==========================================================
- Version without set representation of true/false literals in clauses but instead using only numbers. (dpll2) 
- Clauses are not modified during the work of the algorithm. Assignment is evaluated each time. 
- Formula remembers a queue of unit clauses to speed up unit propagation. (dpll2) 
- Uses stack for the assignment and backpropagation instead of deep copy. (dpll2) 
'''


class Clause:
    """
    The class which represents a single clause.
    """

    def __init__(self, literals):
        self.literals_list = literals  # describes how exactly does this clause look like
        self.literals = set(literals)  # unordered unique set of literals
        self.size = len(self.literals)

    def partial_assignment(self, assignment: Iterable) -> list:
        """
        Performs partial assignment of this clause with give `assignment` and returns the resulting list of literals,
        i.e. if the clause is SAT then returns empty list, otherwise returns the remaining list of unassigned literals.

        :param assignment: the assignment
        :return: if the clause is SAT then returns empty list, otherwise returns the remaining list of unassigned
        literals
        """
        unassigned = set(self.literals)  # set has O(1) remove complexity
        for literal in assignment:
            if literal in self.literals:
                return []

            if -literal in self.literals:
                unassigned.remove(-literal)

        return list(unassigned)

    def is_satisfied(self, assignment: Iterable) -> bool:
        """
        :param: assignment: the assignment
        :return: True if the clause is satisfied in the `assignment`, i.e. one of its literals is True.
        """
        for literal in assignment:
            if literal in self.literals:
                return True

        return False

    def is_unsatisfied(self, assignment: Iterable) -> bool:
        """
        :param: assignment: the assignment
        :return: True if the clause is unsatisfied in the `assignment`, i.e. all of the literals are False.
        """
        false = 0
        for literal in assignment:
            if literal in self.literals:
                return False

            if -literal in self.literals:
                false += 1

        return false == self.size

    def is_unit(self, assignment: Iterable) -> bool:
        """
        :param: assignment: the assignment
        :return: True if the clause is unit in the `assignment`, i.e. only one literal is unassigned and the rest of
        them are False.
        """
        false = 0
        for literal in assignment:
            if literal in self.literals:
                return False

            if -literal in self.literals:
                false += 1

        return false == self.size - 1


class CNFFormula:
    """
    The class which represents one formula in CNF.
    """

    def __init__(self, formula):
        self.formula = formula  # list of lists of literals
        self.clauses = [Clause(literals) for literals in self.formula]  # list of clauses
        # self.literals = set()  # unordered unique set of all literals in the formula
        # self.variables = set()  # unordered unique set of all variables in the formula
        self.unassigned = set()  # unordered unique set of unsigned variables in the formula (clauses use literals)
        self.adjacency_lists = {}  # dictionary with variables as keys and values as lists of clauses with this literal
        self.unit_clauses_queue = deque()  # queue for unit clauses
        self.assignment_stack = deque()  # stack for representing the current assignment for backtracking

        for clause in self.clauses:
            if clause.is_unit([]):
                self.unit_clauses_queue.append(clause)

            # For every literal in clause (*)
            for literal in clause.literals:
                variable = abs(literal)
                # self.literals.add(literal)
                # self.variables.add(variable)
                self.unassigned.add(variable)

                # (*) find out if it already has list of clauses (key) in adjacency_lists. If it does, then update that
                # list with this clause. If it does not, then create new element of dictionary `adjacency_lists` with
                # key being this variable and then create its value as a list with this clause.
                if variable in self.adjacency_lists:
                    if clause not in self.adjacency_lists[variable]:
                        self.adjacency_lists[variable].append(clause)

                else:
                    self.adjacency_lists[variable] = [clause]

    def is_satisfied(self) -> bool:
        """
        :return: True if the formula is satisfied, i.e. if all the clauses are satisfied
        """
        for clause in self.clauses:
            if not clause.is_satisfied(self.assignment_stack):
                return False

        return True

    def partial_assignment(self, assignment: Iterable) -> bool:
        """
        Perform the partial assignment of literals from `assignment` by setting them to True and opposite literals to
        False.

        :param assignment: list of literals to be set to True
        :return: True if the assignment was successful, False otherwise, i.e. one or more clauses are unsatisfied by
                 this assignment.
        """
        for literal in assignment:
            # Remove corresponding variable from the unassigned set of the formula and add literal to assignment stack
            self.unassigned.remove(abs(literal))
            self.assignment_stack.append(literal)

            # For every clause in the adjacency list of this variable find out which
            # clauses become unit and which become unsatisfied in the current assignment
            for clause in self.adjacency_lists[abs(literal)]:
                if clause.is_unsatisfied(self.assignment_stack):
                    return False

                if clause.is_unit(self.assignment_stack):
                    self.unit_clauses_queue.append(clause)

        return True

    def undo_partial_assignment(self, decision_literal: int) -> None:
        """
        Undo partial assignment of this formula by removing literals from `self.assignment` up until the
        `decision_literal`.

        :param decision_literal: the last literal which assignment is undone
        """
        self.unit_clauses_queue.clear()
        while self.assignment_stack:
            literal = self.assignment_stack.pop()
            self.unassigned.add(abs(literal))
            if literal == decision_literal:
                break

    def unit_propagation(self) -> Tuple[list, bool]:
        """
        Performs a unit propagation of this formula.

        :return: a tuple (assignment, success) with assignment containing literals derived by unit propagation and
                 success representing whether the unit propagation was successful, i.e. no clause is unsatisfied by the
                 derived assignment, or False, if at least one clause is unsatisfied.
        """
        propagated_literals = []
        while self.unit_clauses_queue:
            unit_clause = self.unit_clauses_queue.popleft()

            # get the resulting literal from the unit clause given by the current assignment
            literal = unit_clause.partial_assignment(self.assignment_stack)
            propagated_literals += literal
            if not self.partial_assignment(literal):
                return propagated_literals, False

        return propagated_literals, True

    def get_decision_literal(self) -> int:
        """
        Finds the unassigned literal which occurs in the largest number of not satisfied clauses.

        :return: the decision literal
        """
        number_of_clauses = 0
        decision_literal = None
        for variable in self.unassigned:
            positive_clauses = 0
            negative_clauses = 0
            for clause in self.adjacency_lists[variable]:
                if not clause.is_satisfied(self.assignment_stack):
                    unassigned = clause.partial_assignment(self.assignment_stack)
                    if variable in unassigned:
                        positive_clauses += 1

                    if -variable in unassigned:
                        negative_clauses += 1

            if positive_clauses > number_of_clauses and positive_clauses > negative_clauses:
                number_of_clauses = positive_clauses
                decision_literal = variable

            if negative_clauses > number_of_clauses:
                number_of_clauses = negative_clauses
                decision_literal = -variable

        return decision_literal

    def print(self) -> None:
        """
        Prints basic information about the formula.
        """
        # Not used in the dpll program itself.
        print("Formula: ")
        print(self.formula)
        print("Clauses: ")
        for clause in self.clauses:
            print(clause.literals)
        print("Literals: ")
        # print(self.literals)
        print("Variables: ")
        # print(self.variables)
        print("Unassigned variables: ")
        print(self.unassigned)
        print("Adjacency lists: ")
        for variable, adj_list in self.adjacency_lists.items():
            print(variable, ": ")
            for clause in adj_list:
                print(clause.literals)


def dpll(cnf_formula: CNFFormula) -> Tuple[bool, list, int, int]:
    """
    DPLL algorithm for deciding whether the DIMACS CNF formula in the argument `cnf_formula` is satisfiable (SAT) or
    unsatisfiable (UNSAT). In the case of SAT formula, the function also returns a model.

    :param cnf_formula: DIMACS CNF formula
    :return: a tuple (sat, model, num_of_decisions, num_of_unit_prop) which describes whether the formula is SAT,
             what is its model, how many decisions were made during the derivation of the model and how many literals
             were derived by unit propagation
    """
    # Unit propagation
    assignment, succeeded = cnf_formula.unit_propagation()

    # Counters for number of decisions and unit propagations
    num_of_decisions = 0
    num_of_unit_prop = len(assignment)

    if cnf_formula.is_satisfied():
        return True, assignment, num_of_decisions, num_of_unit_prop

    if not succeeded:
        return False, [], num_of_decisions, num_of_unit_prop

    # Find the literal for decision
    decision_literal = cnf_formula.get_decision_literal()

    # Perform the partial assignment of the formula with the decision literal
    cnf_formula.partial_assignment([decision_literal])

    # Recursive call on the resulting formula
    sat, model, decisions, unit_propagations = dpll(cnf_formula)
    num_of_decisions += decisions + 1
    num_of_unit_prop += unit_propagations

    # If the recursive call was successful the formula is SAT
    if sat:
        model += assignment + [decision_literal]
        return True, model, num_of_decisions, num_of_unit_prop

    # If the recursive call was not successful then undo changes and try the opposite value of the decision literal
    cnf_formula.undo_partial_assignment(decision_literal)
    cnf_formula.partial_assignment([-decision_literal])

    # Recursive call on the resulting formula
    sat, model, decisions, unit_propagations = dpll(cnf_formula)
    num_of_decisions += decisions + 1
    num_of_unit_prop += unit_propagations

    # If the recursive call was successful the formula is SAT
    if sat:
        model += assignment + [-decision_literal]
        return True, model, num_of_decisions, num_of_unit_prop

    # Otherwise the formula is UNSAT
    return False, [], num_of_decisions, num_of_unit_prop


def find_model(input_file: str) -> Optional[Tuple[bool, list, float, int, int]]:
    """
    Finds the model of the SAT formula from the `input_file` or returns `UNSAT`.

    :param input_file: describes the input formula. The file can contain either CNF formula in DIMACS format and in
                       that case ends with ".cnf" extension, or NNF formula in simplified SMT-LIB format and ends with
                        ".sat" extension.
    :return: a tuple (sat, model, cpu_time, decisions_count, unit_prop_count) which describes whether the formula is SAT
             or UNSAT, what is its model, how long the computation took, number of decisions and number of literals
             derived by unit propagation
    """
    if input_file[-3:] == "sat":
        formula2cnf(input_file=input_file, output_file=input_file[:-4] + ".cnf", left_to_right=True)
        input = open(input_file[:-4] + ".cnf", mode="r")

    elif input_file[-3:] == "cnf":
        input = open(input_file, mode="r")

    else:
        print("Unsupported file extension. File extension must be `.cnf` for DIMACS, or `.sat` for the simplified "
              "SMT-LIB format.")
        return

    dimacs_formula = input.read()
    dimacs_formula = dimacs_formula.splitlines()

    formula = [list(map(int, clause[:-2].strip().split())) for clause in dimacs_formula if clause != "" and
               clause[0] not in ["c", "p", "%", "0"]]

    cnf_formula = CNFFormula(formula)
    start_time = time.time()
    sat, model, decisions_count, unit_prop_count = dpll(cnf_formula)
    cpu_time = time.time() - start_time
    if sat:
        model.sort(key=abs)
        print("SAT")
        print("Model =", model)
        print("Possible missing literals can have arbitrary value.")

    else:
        print("UNSAT")

    print("Total CPU time =", cpu_time, "seconds")
    print("Number of decisions =", decisions_count)
    print("Number of steps of unit propagation =", unit_prop_count)

    return sat, model, cpu_time, decisions_count, unit_prop_count


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", default=None, type=str, help="Input file which contains a description of a "
                                                                "formula.")
    args = parser.parse_args()

    find_model(input_file=args.input)
