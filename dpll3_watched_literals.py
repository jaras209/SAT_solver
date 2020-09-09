import argparse
from formula2cnf import formula2cnf
import time
from typing import Tuple, Optional, Iterable
from collections import deque

'''
====================================== dpll3_watched_literals ===================================================
- Version with watched literals based on version dpll3
'''


class Clause:
    """
    The class which represents a single clause.
    """

    def __init__(self, literals):
        self.literals = literals  # describes how exactly does this clause look like
        self.size = len(self.literals)
        self.w1 = None
        self.w2 = None

        if len(self.literals) > 1:
            self.w1 = 0
            self.w2 = 1

        elif len(self.literals) > 0:
            self.w1 = self.w2 = 0

    def partial_assignment(self, assignment: list) -> list:
        """
        Performs partial assignment of this clause with given `assignment` and returns the resulting list of literals,
        i.e. if the clause is SAT then returns empty list, otherwise returns the remaining list of unassigned literals.
        (It it currently used only in the heuristic selection of decision literal: `get_decision_literal`)

        :param assignment: the assignment
        :return: if the clause is SAT then returns empty list, otherwise returns the remaining list of unassigned
        literals
        """
        unassigned = []
        for literal in self.literals:
            if assignment[abs(literal)] == literal:
                return []

            if assignment[abs(literal)] == 0:
                unassigned.append(literal)

        return list(unassigned)

    def update_watched_literal(self, assignment: list, new_variable: int) -> Tuple[bool, int, Optional[int]]:
        """
        Updates the watched literal of this Clause given the assignment `assignment` and the latest assigned variable
        `new_variable` which is used to update the watched literal, if necessary.

        :param new_variable: name of the variable which was currently changed
        :param assignment: a current assignment list
        :return: Tuple `(success, new_watched_literal, unit_clause literal)` where `success` represents whether the
        update was successful or the Clause is unsatisfied, `new_watched_literal` is the new watched literal,
        `unit_clause_literal` represent the unit clause literal in the case that the Clause becomes unit during the
        update of the watched literal.
        """

        # Without loss of generality, the old watched literal index, that we need to change, is `self.w1`
        if new_variable == abs(self.literals[self.w2]):
            temp = self.w1
            self.w1 = self.w2
            self.w2 = temp

        # If Clause[self.w1] is True in this new variable assignment or
        # Clause[self.w2] has been True previously, then the Clause is satisfied
        if (self.literals[self.w1] == assignment[abs(self.literals[self.w1])] or
                self.literals[self.w2] == assignment[abs(self.literals[self.w2])]):
            return True, self.literals[self.w1], None

        # If Clause[self.w1] is False in this new variable assignment and
        # Clause[self.w2] is also False from previous assignment, then the Clause is unsatisfied
        if (-self.literals[self.w1] == assignment[abs(self.literals[self.w1])] and
                -self.literals[self.w2] == assignment[abs(self.literals[self.w2])]):
            return False, self.literals[self.w1], None

        # If Clause[self.w1] is False in this new variable assignment and
        # Clause[self.w2] is still unassigned, then look for new index of the watched literal `self.w1`
        if (-self.literals[self.w1] == assignment[abs(self.literals[self.w1])] and
                assignment[abs(self.literals[self.w2])] == 0):
            old_w1 = self.w1
            for w in [(self.w1 + i) % self.size for i in range(self.size)]:
                # new index `w` must not be equal to `self.w2` and
                # Clause[w] cannot be False in the current assignment
                if w == self.w2 or -self.literals[w] == assignment[abs(self.literals[w])]:
                    continue

                self.w1 = w
                break

            # If the new watched literal index `self.w1` has not been found then the Clause is unit with
            # Clause[self.w2] being the only unassigned literal.
            if self.w1 == old_w1:
                return True, self.literals[self.w1], self.literals[self.w2]

            # Otherwise the state of the Clause is either not-yet-satisfied or satisfied -> both not important
            return True, self.literals[self.w1], None

    def is_satisfied(self, assignment: list) -> bool:
        """
        (It it currently used only in the heuristic selection of decision literal: `get_decision_literal`)
        :param: assignment: the assignment list
        :return: True if the clause is satisfied in the `assignment`, i.e. one of its watched literals is True.
        """
        return (self.literals[self.w1] == assignment[abs(self.literals[self.w1])] or
                self.literals[self.w2] == assignment[abs(self.literals[self.w2])])

    '''
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
    '''


class CNFFormula:
    """
    The class which represents one formula in CNF.
    """

    def __init__(self, formula):
        self.formula = formula  # list of lists of literals
        self.clauses = [Clause(literals) for literals in self.formula]  # list of clauses
        self.variables = set()  # unordered unique set of variables in the formula
        self.watched_lists = {}  # dictionary: list of clauses with this `key` literal being watched
        self.unit_clauses_queue = deque()  # queue for unit clauses
        self.assignment_stack = deque()  # stack for representing the current assignment for backtracking
        self.assignment = None  # the assignment list with `variable` as indices and `+variable/-variable/0` as values

        for clause in self.clauses:
            # If the clause is unit right at the start, add it to the unit clauses queue
            if clause.w1 == clause.w2:
                self.unit_clauses_queue.append(clause.literals[clause.w1])

            # For every literal in clause:
            for literal in clause.literals:
                variable = abs(literal)
                # - add variable to the set of all variables
                self.variables.add(variable)

                # - Create empty list of watched clauses for this variable, if it does not exist yet
                if variable not in self.watched_lists:
                    self.watched_lists[variable] = []

                # - Update the list of watched clauses for this variable
                if clause.literals[clause.w1] == literal or clause.literals[clause.w2] == literal:
                    if clause not in self.watched_lists[variable]:
                        self.watched_lists[variable].append(clause)

        # Set the assignment list of the Formula with values 0 (unassigned) for every variable
        max_variable = max(map(abs, self.variables))
        self.assignment = [0]*(max_variable + 1)

    def is_satisfied(self) -> bool:
        """
        :return: True if the formula is satisfied, i.e. if all variables are assigned
        """
        return len(self.variables) == len(self.assignment_stack)

    def partial_assignment(self, assignment: Iterable) -> bool:
        """
        Perform the partial assignment of literals from `assignment` by setting them to True and opposite literals to
        False.

        :param assignment: list of literals to be set to True
        :return: True if the assignment was successful, False otherwise, i.e. one or more clauses are unsatisfied by
                 this assignment.
        """
        for literal in assignment:
            # Add literal to assignment stack and set the value of corresponding variable in the assignment dictionary
            self.assignment_stack.append(literal)
            self.assignment[abs(literal)] = literal

            # Copy the watched list of this literal because we need to delete some of the clauses from it during
            # iteration and that cannot be done while iterating through the same list
            watched_list = self.watched_lists[abs(literal)][:]

            # For every clause in the watched list of this variable perform the update of the watched literal and
            # find out which clauses become unit and which become unsatisfied in the current assignment
            for clause in watched_list:
                success, watched_literal, unit_clause = clause.update_watched_literal(self.assignment, abs(literal))

                # If the clause is not unsatisfied:
                if success:
                    # If the watched literal was changed:
                    if abs(watched_literal) != abs(literal):
                        # Add this clause to the watched list of the new watched literal
                        if clause not in self.watched_lists[abs(watched_literal)]:
                            self.watched_lists[abs(watched_literal)].append(clause)

                        # Remove this clause from the watched list of the old watched literal
                        self.watched_lists[abs(literal)].remove(clause)

                    # If the clause is unit then add the corresponding unassigned literal to the unit clauses queue
                    if unit_clause:
                        if unit_clause not in self.unit_clauses_queue:
                            self.unit_clauses_queue.append(unit_clause)

                # If the clause is unsatisfied return False
                if not success:
                    return False

        return True

    def undo_partial_assignment(self, decision_literal: int) -> None:
        """
        Undo partial assignment of this formula by removing literals from `self.assignment_stack` up until the
        `decision_literal` and setting values of the corresponding variables in `self.assignment` to 0.

        :param decision_literal: the last literal which assignment is undone
        """
        self.unit_clauses_queue.clear()
        while self.assignment_stack:
            literal = self.assignment_stack.pop()
            self.assignment[abs(literal)] = 0
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
            unit_clause_literal = self.unit_clauses_queue.popleft()
            propagated_literals.append(unit_clause_literal)
            if not self.partial_assignment([unit_clause_literal]):
                return propagated_literals, False

        return propagated_literals, True

    def get_decision_literal(self) -> int:
        """
        Finds the unassigned literal which occurs in the largest number of not satisfied clauses.

        :return: the decision literal
        """
        number_of_clauses = -1
        decision_literal = None
        for variable in self.variables:
            if self.assignment[variable] == 0:
                positive_clauses = 0
                negative_clauses = 0
                for clause in self.watched_lists[variable]:
                    if not clause.is_satisfied(self.assignment):
                        unassigned = clause.partial_assignment(self.assignment)
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

        print("Variables: ")
        print(self.variables)
        print("Watched lists: ")
        for variable, adj_list in self.watched_lists.items():
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

    if not succeeded:
        return False, [], num_of_decisions, num_of_unit_prop

    if cnf_formula.is_satisfied():
        return True, assignment, num_of_decisions, num_of_unit_prop

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
