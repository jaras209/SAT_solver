import argparse
from typing import Optional
from cdcl_heuristic import CNFFormula
from cdcl_heuristic import cdcl
import heapq


def find_backbones(input_file: str) -> Optional[list]:
    if input_file[-3:] == "cnf":
        input = open(input_file, mode="r")

    else:
        print("Unsupported file extension. File extension must be `.cnf` for DIMACS")
        return

    dimacs_formula = input.read()
    dimacs_formula = dimacs_formula.splitlines()

    formula = [list(map(int, clause[:-2].strip().split())) for clause in dimacs_formula if clause != "" and
               clause[0] not in ["c", "p", "%", "0"]]

    cnf_formula = CNFFormula(formula)
    sat, model, decisions, unit_propagations, restarts = cdcl(cnf_formula)

    if not sat:
        print("Formula is UNSAT")
        return

    candidates = []

    for literal in model:
        count = 0
        for clause in formula:
            if literal in clause:
                count += 1

        candidates.append([-count, literal])

    heapq.heapify(candidates)
    backbones = []

    while candidates:
        priority, literal = heapq.heappop(candidates)
        if literal == 0:
            continue

        cnf_formula = CNFFormula(formula + [[-literal]])
        sat, model, decisions, unit_propagations, restarts = cdcl(cnf_formula)

        if not sat:
            backbones.append(literal)
            formula.append([literal])

        else:
            temp = set(model)
            for c in candidates:
                if c[1] not in temp:
                    c[1] = 0

    if backbones:
        backbones.sort(key=abs)
        print(backbones)

    else:
        print("There are no backbones")
    return backbones


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=str, help="Input file which contains a description of a formula.")
    args = parser.parse_args()

    find_backbones(args.input)
