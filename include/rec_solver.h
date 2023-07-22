#ifndef REC_SOLVER_H
#define REC_SOLVER_H
#include "z3++.h"
#include <map>

class rec_solver {
    private:
        z3::context& z3ctx;
        std::map<z3::expr, z3::expr> rec_eqs;
        std::map<z3::expr, z3::expr> res;
    public:
        rec_solver(std::map<z3::expr, z3::expr>& rec_eqs, z3::context& z3ctx);
        rec_solver(z3::context& z3ctx): z3ctx(z3ctx) {}
        void set_eqs(std::map<z3::expr, z3::expr>& rec_eqs);
        void simple_solve();
};
#endif