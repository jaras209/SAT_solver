import argparse
from formula2cnf import formula2cnf
import copy


class Clause:
    def __init__(self, literals):
        self.literals = literals  # describes how exactly does the clause appear in the formula
        # self.variables = set(map(abs, self.literals))  # unordered unique set of variables
        self.unassigned = set(self.literals)  # unordered unique set of unassigned literals
        self.true = set()  # unordered unique set of True literals
        self.false = set()  # # unordered unique set of False literals
        self.size = len(self.unassigned)  # number of literals in the clause

    def partial_assignment(self, literal):
        if literal in self.unassigned:
            self.true.add(literal)
            self.unassigned.remove(literal)

        if -literal in self.unassigned:
            self.false.add(-literal)
            self.unassigned.remove(-literal)

    def is_satisfied(self):
        return len(self.true) > 0

    def is_unsatisfied(self):
        return len(self.false) == self.size

    def is_unit(self):
        return len(self.unassigned) == 1 and len(self.false) == self.size - 1


class CNFFormula:
    def __init__(self, formula):
        self.formula = formula  # list of lists of literals
        self.clauses = [Clause(literals) for literals in self.formula]  # list of clauses
        self.literals = set()  # unordered unique set of all literals in the formula
        self.variables = set()  # unordered unique set of all variables in the formula
        self.unassigned = set()
        self.adjacency_lists = {}  # dictionary with keys as variables and values as lists of clauses with this literal
        for clause in self.clauses:
            for literal in clause.literals:
                self.literals.add(literal)
                variable = abs(literal)
                self.variables.add(variable)
                self.unassigned.add(variable)

                #  for every literal in clause, find out if it already has (key) its list in adjacency_lists. If
                #  it does, then update that list with this clause (maybe check if this clause is not an element of
                #  that list already for duplicity in case of one clause having two literals from the same variable,
                #  which could actually happen). If it does not, then create new element of dictionary
                #  adjacency_lists with key of this variable and then create its value as a list with this clause.
                if variable in self.adjacency_lists:
                    if clause not in self.adjacency_lists[variable]:
                        self.adjacency_lists[variable].append(clause)

                else:
                    self.adjacency_lists[variable] = [clause]

    def is_satisfied(self):
        for clause in self.clauses:
            if not clause.is_satisfied():
                return False

        return True

    def partial_assignment(self, assignment):
        for literal in assignment:
            self.unassigned.remove(abs(literal))
            for clause in self.adjacency_lists[abs(literal)]:
                clause.partial_assignment(literal)
                if clause.is_unsatisfied():
                    return False

        return True

    def get_unit_clause(self):
        for clause in self.clauses:
            if clause.is_unit():
                return clause

        return None

    def unit_propagation(self):
        assignment = []
        unit_clause = self.get_unit_clause()
        while unit_clause is not None:
            assignment += list(unit_clause.unassigned)
            if not self.partial_assignment(list(unit_clause.unassigned)):
                return assignment, False

            unit_clause = self.get_unit_clause()

        return assignment, True

    def get_decision_literal(self):
        number_of_clauses = 0
        branching_variable = None
        for variable in self.unassigned:
            positive_clauses = 0
            negative_clauses = 0
            for clause in self.adjacency_lists[variable]:
                if variable in clause.unassigned:
                    positive_clauses += 1

                if -variable in clause.unassigned:
                    negative_clauses += 1

            if positive_clauses > number_of_clauses and positive_clauses > negative_clauses:
                number_of_clauses = positive_clauses
                branching_variable = variable

            if negative_clauses > number_of_clauses:
                number_of_clauses = negative_clauses
                branching_variable = -variable

        return branching_variable

    def print(self):
        print("Formula: ")
        print(self.formula)
        print("Clauses: ")
        for clause in self.clauses:
            print(clause.literals)
        print("Literals: ")
        print(self.literals)
        print("Variables: ")
        print(self.variables)
        print("Adjacency lists: ")
        for variable, adj_list in self.adjacency_lists.items():
            print(variable, ": ")
            for clause in adj_list:
                print(clause.literals)


def find_model(cnf_formula):
    assignment, success = cnf_formula.unit_propagation()
    if cnf_formula.is_satisfied():
        return assignment

    if not success:
        return None

    literal = cnf_formula.get_decision_literal()
    old_cnf_formula = copy.deepcopy(cnf_formula)

    cnf_formula.partial_assignment([literal])
    result = find_model(cnf_formula)
    if result:
        return assignment + result + [literal]

    cnf_formula = old_cnf_formula
    cnf_formula.partial_assignment([-literal])
    result = find_model(cnf_formula)
    if result:
        return assignment + result + [-literal]

    return None


def dpll(input_file=None):
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
    formula = [list(map(int, clause[:-2].strip().split())) for clause in dimacs_formula if clause[0] not in ["c", "p"]]

    cnf_formula = CNFFormula(formula)
    assignment = find_model(cnf_formula)
    if assignment:
        assignment.sort(key=abs)

    print(assignment)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", default=None, type=str, help="Input file which contains a description of a "
                                                                "formula in NNF")
    args = parser.parse_args()

    dpll(input_file=args.input)
