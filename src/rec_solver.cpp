#include "rec_solver.h"

bool is_simple_rec(z3::func_decl func_decl, z3::expr rhs) {
    
    std::all_of(rhs.args().begin(), )
}

rec_solver::rec_solver(std::map<z3::expr, z3::expr>& eqs, z3::context& z3ctx): z3ctx(z3ctx) {
    set_eqs(eqs);
}

void rec_solver::set_eqs(std::map<z3::expr, z3::expr>& eqs) {
    rec_eqs = eqs;
}

void rec_solver::simple_solve() {
    for (auto& func_eq : rec_eqs) {
        z3::expr func = func_eq.first;
        z3::expr eq = func_eq.second;
        func.decl().kind() == Z3_OP_ADD
    }
}