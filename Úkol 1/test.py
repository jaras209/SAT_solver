

if __name__ == "__main__":
    string_formula = "(and (or (and (or x1 (not x4)) (or x3 x9)) (and (or x7 x1) (or x4 x9))) (or (and (or x9 x9) (or (not x4) (not x5))) (and (or x3 (not x6)) (or (not x3) x6))))"
    formula = string_formula.replace("(", "( ").replace(")", " )")
    print(formula)
    formula = formula.split()
    print(formula)
    for e in formula:
        print(e)