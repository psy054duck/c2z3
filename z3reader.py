import z3

def main():
    f = z3.parse_smt2_file('tmp/tmp.smt2')
    for e in f:
        print(z3.simplify(e))

if __name__ == '__main__':
    main()