#ifndef REC_SOLVER_H
#define REC_SOLVER_H
#include "z3++.h"
#include <map>

class rec_solver {
    private:
        z3::context& z3ctx;
        z3::expr_vector rec_eqs;
        std::map<z3::expr, z3::expr> res;
    public:
        rec_solver(z3::expr_vector& rec_eqs, z3::context& z3ctx): rec_eqs(rec_eqs), z3ctx(z3ctx) {}
        rec_solver(z3::context& z3ctx): z3ctx(z3ctx), rec_eqs(z3ctx) {}
        void set_eqs(z3::expr_vector& rec_eqs);
        void solve();
};
#endif