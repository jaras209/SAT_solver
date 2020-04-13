import argparse


class FormulaTree:
    def __init__(self, root, left=None, right=None):
        self.root = root
        self.left = left
        self.right = right

        #bla bla bla


if __name__ == "__main__":
    # Parse arguments
    parser = argparse.ArgumentParser()
    parser.add_argument("--input_file", default=None, type=str, help="Input file which contains a description of a single formula in NNF")
    args = parser.parse_args()

    with open(args.input_file, mode="r") as input_file:
        