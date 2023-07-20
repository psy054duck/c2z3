import z3

def main():
    f = z3.parse_smt2_file('tmp/tmp0.smt2')
    solver = z3.Solver()
    solver.add(f)
    print(solver.check())

if __name__ == '__main__':
    main()