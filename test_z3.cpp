#include "z3++.h"
#include <iostream>

int main() {
    z3::context c;
    z3::expr x = c.int_const("x");
    z3::expr y = c.int_const("y");

    z3::solver s(c);
    z3::expr conjecture = (x + y > 0);
    s.add(conjecture);
    if (s.check() == z3::sat) {
        std::cout << s.get_model() << std::endl;
    }
}