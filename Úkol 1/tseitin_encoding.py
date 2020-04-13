import argparse


class Formula:
    def __init__(self):
        self.root = None
        self.left = None
        self.right = None
        self.string_formula = None

    def create_formula_from_string(self, string_formula):
        self.string_formula = string_formula

        while string_formula:
            e = string_formula[0]
            string_formula = string_formula[1:]

            if e == ")":
                break

            elif e in ["and", "or"]:
                self.root = e
                self.left, string_formula = self._recursive_formula_construction(string_formula)
                self.right, string_formula = self._recursive_formula_construction(string_formula)

            elif e == "not":
                self.root = e
                self.left, string_formula = self._recursive_formula_construction(string_formula)

            elif e != "(":
                self.root = e

    def _recursive_formula_construction(self, string_formula):
        sub_formula = Formula()
        sub_formula.string_formula = string_formula

        while string_formula:
            e = string_formula[0]
            string_formula = string_formula[1:]

            if e == ")":
                return sub_formula, string_formula

            elif e in ["and", "or"]:
                sub_formula.root = e
                sub_formula.left, string_formula = sub_formula._recursive_formula_construction(string_formula)
                sub_formula.right, string_formula = sub_formula._recursive_formula_construction(string_formula)

            elif e == "not":
                sub_formula.root = e
                sub_formula.left, string_formula = sub_formula._recursive_formula_construction(string_formula)

            elif e != "(":
                sub_formula.root = e
                return sub_formula, string_formula


    def print_formula(self, i = 0):
        print("Level: ", i, "Value: ", self.root)
        if self.left:
            self.left.print_formula(i=i+1)
        if self.right:
            self.right.print_formula(i=i+1)


if __name__ == "__main__":
    # Parse arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("input_file", default=None, type=str, help="Input file which contains a description of a single formula in NNF")
    args = parser.parse_args()

    with open(args.input_file, mode="r") as input_file:
        string_formula = input_file.read().replace("(", "( ").replace(")", " )")
        print(string_formula)
        string_formula = string_formula.split()
        print(string_formula)

        formula = Formula()
        formula.create_formula_from_string(string_formula)
        formula.print_formula()