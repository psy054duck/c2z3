#include "llvm/IRReader/IRReader.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/Transforms/Utils/LCSSA.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/Transforms/Utils/InstructionNamer.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/AggressiveInstCombine/AggressiveInstCombine.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include "z3++.h"

#include <string>
#include <vector>
#include <map>
#include <set>
#include <fstream>

using namespace llvm;

typedef std::vector<BasicBlock*> BBPath;
z3::expr_vector handle_loop(const Loop* loop, std::vector<const Value*>& visited, const LoopInfo& LI, const DominatorTree& DT, const PostDominatorTree& PDT, std::set<const Loop*> loops, z3::context& z3ctx);

void abortWithInfo(const std::string &s) {
    errs() << s << "\n";
    abort();
}

void combine_vec(z3::expr_vector& vec1, const z3::expr_vector& vec2) {
    for (z3::expr e : vec2) {
        vec1.push_back(e);
    }
}

// only works for Use
z3::expr use2z3(const Use& u, const LoopInfo& LI, z3::context &z3ctx, bool from_latch = false) {
    z3::expr res(z3ctx);
    const Value* v = u.get();
    const User* user = u.getUser();
    const Instruction* userInst = dyn_cast<Instruction>(user);
    const BasicBlock* userBB = userInst->getParent();
    Type* vTy = v->getType();

    if (auto CI = dyn_cast<ConstantInt>(v)) {
        bool isBoolTy = vTy->isIntegerTy(1);
        if (isBoolTy) {
            res = z3ctx.bool_val(*CI->getValue().getRawData() != 0);
        } else {
            res = z3ctx.int_val(CI->getSExtValue());
        }
    // } else if (auto CI = dyn_cast<ICmpInst>(v)) {
    } else {
        z3::expr_vector args(z3ctx);
        z3::sort_vector sorts(z3ctx);
        int userDepth = LI.getLoopDepth(userBB);
        const Instruction* defInst = dyn_cast<Instruction>(v);
        const BasicBlock* defBB = defInst->getParent();
        int defDepth = LI.getLoopDepth(defBB);
        for (int i = 0; i < defDepth - 1; i++) {
            sorts.push_back(z3ctx.int_sort());
            std::string idx = std::string("n") + std::to_string(i);
            args.push_back(z3ctx.int_const(idx.data()));
        }

        if (defDepth > 0) {
            sorts.push_back(z3ctx.int_sort());
            std::string idx = std::string("n") + std::to_string(defDepth - 1);
            if (userDepth < defDepth) {
                idx = std::string("N") + std::to_string(defDepth - 1);
                args.push_back(z3ctx.int_const(idx.data()));
            } else {
                if (from_latch) {
                    args.push_back(z3ctx.int_const(idx.data()));
                } else {
                    args.push_back(z3ctx.int_const(idx.data()) + 1);
                }
            }
        }
        bool isBoolTy = vTy->isIntegerTy(1);
        z3::sort ret_sort = isBoolTy ? z3ctx.bool_sort() : z3ctx.int_sort();
        z3::func_decl func_sig = z3ctx.function(v->getName().data(), sorts, ret_sort);
        res = func_sig(args);
    }
    return res;
}

z3::expr def2z3(const Value* v, const LoopInfo& LI, z3::context &z3ctx) {
    z3::expr res(z3ctx);
    Type* vTy = v->getType();
    const Instruction* inst = dyn_cast<Instruction>(v);
    const BasicBlock* bb = inst->getParent();
    int depth = LI.getLoopDepth(bb);
    z3::sort_vector sorts(z3ctx);
    z3::expr_vector args(z3ctx);
    for (int i = 0; i < depth - 1; i++) {
        sorts.push_back(z3ctx.int_sort());
        std::string idx = std::string("n") + std::to_string(i);
        args.push_back(z3ctx.int_const(idx.data()));
    }
    if (depth > 0) {
        sorts.push_back(z3ctx.int_sort());
        std::string idx = std::string("n") + std::to_string(depth - 1);
        args.push_back(z3ctx.int_const(idx.data()) + 1);
    }
    if (auto CI = dyn_cast<ConstantInt>(v)) {
        bool isBoolTy = vTy->isIntegerTy(1);
        if (isBoolTy) {
            res = z3ctx.bool_val(*CI->getValue().getRawData() != 0);
        } else {
            res = z3ctx.int_val(CI->getSExtValue());
        }
    // } else if (auto CI = dyn_cast<ICmpInst>(v)) {
    //     res = z3ctx.bool_const(v->getName().data());
    } else {
        bool isBoolTy = vTy->isIntegerTy(1);
        z3::sort ret_sort = isBoolTy ? z3ctx.bool_sort() : z3ctx.int_sort();
        z3::func_decl func_sig = z3ctx.function(v->getName().data(), sorts, ret_sort);
        res = func_sig(args);
        // if (isBoolTy) {
        //     res = z3ctx.bool_const(v->getName().data());
        // } else {
        //     res = z3ctx.int_const(v->getName().data());
        // }
    }
    return res;
}

std::vector<const Use*> collectAllAssertions(Function& f) {
    std::vector<const Use*> assertions;
    for (const auto& bb : f) {
        for (const auto& inst : bb) {
            unsigned opcode = inst.getOpcode();
            if (opcode == Instruction::Call) {
                auto callStmt = dyn_cast<CallInst>(&inst);
                Function* calledFunction = callStmt->getCalledFunction();
                StringRef funcName = calledFunction->getName();
                if (funcName.endswith("assert")) {
                    assertions.push_back(&callStmt->getArgOperandUse(0));
                }
            }
        }
    }
    return assertions;
}

z3::expr_vector inst2z3(const Instruction* inst, const LoopInfo& LI, const DominatorTree& DT, const PostDominatorTree& PDT, std::set<const Loop*>& loops, z3::context& z3ctx) {
    auto opcode = inst->getOpcode();
    z3::expr_vector res(z3ctx);
    z3::expr cur_expr(z3ctx, z3ctx.bool_val(true));
    static int call_index = 0;
    if (inst->isBinaryOp()) {
        z3::expr lhs = def2z3(inst, LI, z3ctx);
        z3::expr operand0 = use2z3(inst->getOperandUse(0), LI, z3ctx);
        z3::expr operand1 = use2z3(inst->getOperandUse(1), LI, z3ctx);
        if (opcode == Instruction::Add) {
            cur_expr = (lhs == operand0 + operand1);
        } else if (opcode == Instruction::Sub) {
            cur_expr = (lhs == operand0 - operand1);
        } else if (opcode == Instruction::Mul) {
            cur_expr = (lhs == operand0 * operand1);
        }
        res.push_back(cur_expr);
    } else if (opcode == Instruction::Select) {
        z3::expr lhs = def2z3(inst, LI, z3ctx);
        z3::expr pred = z3ctx.bool_const(inst->getOperand(0)->getName().data());
        z3::expr true_v = use2z3(inst->getOperandUse(1), LI, z3ctx);
        z3::expr false_v = use2z3(inst->getOperandUse(2), LI, z3ctx);
        cur_expr = (lhs == z3::ite(pred, true_v, false_v));
        res.push_back(cur_expr);
    } else if (opcode == Instruction::ICmp) {
        z3::expr lhs = def2z3(inst, LI, z3ctx);
        z3::expr operand0 = use2z3(inst->getOperandUse(0), LI, z3ctx);
        z3::expr operand1 = use2z3(inst->getOperandUse(1), LI, z3ctx);
        if (auto ci = dyn_cast<ICmpInst>(inst)) {
            auto pred = ci->getPredicate();
            if (ICmpInst::isLT(pred)) {
                cur_expr = (lhs == operand0 < operand1);
            } else if (ICmpInst::isLE(pred)) {
                cur_expr = (lhs == operand0 <= operand1);
            } else if (ICmpInst::isGT(pred)) {
                cur_expr = (lhs == operand0 > operand1);
            } else if (ICmpInst::isGE(pred)) {
                cur_expr = (lhs == operand0 >= operand1);
            } else if (ICmpInst::isEquality(pred)) {
                cur_expr = (lhs == (operand0 == operand1));
            }
        }
        res.push_back(cur_expr);
    } else if (opcode == Instruction::PHI) {
        assert(inst->getType()->isIntegerTy());
        const PHINode* PN = dyn_cast<PHINode>(inst);
        const BasicBlock* bb = inst->getParent();
        int depth = LI.getLoopDepth(bb);
        z3::sort_vector sorts(z3ctx);
        z3::expr_vector args_0(z3ctx);
        z3::expr_vector args_N(z3ctx);
        z3::expr_vector args_n_1(z3ctx);
        for (int i = 0; i < depth - 1; i++) {
            std::string idx = std::string("n") + std::to_string(i);
            sorts.push_back(z3ctx.int_sort());
            args_0.push_back(z3ctx.int_const(idx.data()));
            args_N.push_back(z3ctx.int_const(idx.data()));
            args_n_1.push_back(z3ctx.int_const(idx.data()));
        }
        if (depth > 0) {
            sorts.push_back(z3ctx.int_sort());
            args_0.push_back(z3ctx.int_val(0));
            std::string N = std::string("N") + std::to_string(depth - 1);
            args_N.push_back(z3ctx.int_const(N.data()));
            std::string idx = std::string("n") + std::to_string(depth - 1);
            args_n_1.push_back(z3ctx.int_const(idx.data()) + 1);
        }
        z3::func_decl func_sig = z3::function(inst->getName().data(), sorts, z3ctx.int_sort());
        for (int i = 0; i < PN->getNumIncomingValues(); i++) {
            const Use& incoming_u = PN->getOperandUse(i);
            const BasicBlock* incoming_b = PN->getIncomingBlock(i);
            if (depth > LI.getLoopDepth(incoming_b)) { // initial values
                cur_expr = (func_sig(args_0) == use2z3(incoming_u, LI, z3ctx));
            } else if (depth == LI.getLoopDepth(incoming_b)) {
                const Loop* someLoop = LI.getLoopFor(incoming_b);
                if (someLoop) { // inductive values
                    bool from_latch = someLoop->isLoopLatch(incoming_b);
                    cur_expr = (def2z3(inst, LI, z3ctx) == use2z3(incoming_u, LI, z3ctx, from_latch));
                } else { // 
                    cur_expr = (def2z3(inst, LI, z3ctx) == use2z3(incoming_u, LI, z3ctx));
                }
            } else {
                cur_expr = (def2z3(inst, LI, z3ctx) == use2z3(incoming_u, LI, z3ctx));
            }
            res.push_back(cur_expr);
        }
    }
    z3::expr_vector globally_quantified(z3ctx);
    int depth = LI.getLoopDepth(inst->getParent());
    z3::expr_vector ret(z3ctx);
    for (int i = 0; i < depth; i++) {
        std::string name = std::string("n") + std::to_string(i);
        z3::expr n = z3ctx.int_const(name.data());
        globally_quantified.push_back(n);
    }
    for (int i = 0; i < res.size(); i++) {
        if (depth > 0) {
            const Loop* loop = LI.getLoopFor(inst->getParent());
            ret.push_back(z3::forall(globally_quantified, res[i]));
            // loops.insert(loop);
        } else {
            ret.push_back(res[i]);
        }
    }
    return ret;
}

z3::expr_vector rel2z3(const Value* v, std::vector<const Value*>& visited, const LoopInfo& LI, const DominatorTree& DT, const PostDominatorTree& PDT, std::set<const Loop*>& loops, z3::context& z3ctx) {
    z3::expr_vector res(z3ctx);
    // errs() << v->getName() << "\n";
    if (std::find(visited.begin(), visited.end(), v) != visited.end()) {
        return res;
    }
    visited.push_back(v);
    if (auto inst = dyn_cast<Instruction>(v) ) {
        if (const Loop* loop = LI.getLoopFor(inst->getParent())) {
            if (loops.find(loop) == loops.end()) {
                loops.insert(loop);
                z3::expr_vector loop_ret = handle_loop(loop, visited, LI, DT, PDT, loops, z3ctx);
                combine_vec(res, loop_ret);
            }
        }
        unsigned opcode = inst->getOpcode();
        if (opcode == Instruction::Call) {
            return res;
        }
        if (opcode == Instruction::PHI) {
            const PHINode* phi = dyn_cast<PHINode>(inst);
            if (phi->getNumIncomingValues() == 2) {
                IRBuilder<> builder(v->getContext());
                const BasicBlock* curB = phi->getParent();
                const BasicBlock* bb0 = phi->getIncomingBlock(0);
                const BasicBlock* bb1 = phi->getIncomingBlock(1);
                const BasicBlock* domB = DT.findNearestCommonDominator(bb0, bb1);
                if (PDT.dominates(curB, domB)) {
                    const Instruction* term = domB->getTerminator();
                    const BranchInst* branch = dyn_cast<BranchInst>(term);
                    if (branch && branch->isConditional()) {
                        Value* condV = branch->getCondition();
                        const BasicBlock* true_b = bb0;
                        const BasicBlock* false_b = bb1;
                        if (DT.dominates(branch->getSuccessor(0), bb0) || DT.dominates(branch->getSuccessor(1), bb1)) {
                            true_b = bb0;
                            false_b = bb1;
                        } else {
                            true_b = bb1;
                            false_b = bb0;
                        }
                        int true_idx = phi->getBasicBlockIndex(true_b);
                        int false_idx = phi->getBasicBlockIndex(false_b);
                        Value* new_select = builder.CreateSelect(condV, phi->getIncomingValue(true_idx), phi->getIncomingValue(false_idx));
                        new_select->setName(v->getName());
                        inst = dyn_cast<Instruction>(new_select);
                        // ReplaceInstWithInst(phi, dyn_cast<Instruction>(new_select));
                        // phi->replaceAllUsesWith(new_select);
                        // new_select->takeName(phi);
                        // phi->eraseFromParent();
                        // errs() << *dyn_cast<Instruction>(new_select) << "\n";
                    }
                }
            }
        }
        z3::expr_vector cur_expr_vec = inst2z3(inst, LI, DT, PDT, loops, z3ctx);
        combine_vec(res, cur_expr_vec);
        // res.push_back(cur_expr);
        for (const Use& u : inst->operands()) {
            const Value* operand_v = u.get();
            z3::expr_vector operand_expr_vec = rel2z3(operand_v, visited, LI, DT, PDT, loops, z3ctx);
            combine_vec(res, operand_expr_vec);
        }
    }
    return res;
}

z3::expr_vector handle_loop(const Loop* loop, std::vector<const Value*>& visited, const LoopInfo& LI, const DominatorTree& DT, const PostDominatorTree& PDT, std::set<const Loop*> loops, z3::context& z3ctx) {
    z3::expr_vector res(z3ctx);
    SmallVector<BasicBlock*> exitingBBs;
    loop->getExitingBlocks(exitingBBs);
    // z3::expr_vector exitConds(z3ctx);
    std::vector<const Value*> exitConds;
    std::vector<bool> true_or_false;
    for (const auto bb : exitingBBs) {
        const Instruction* terminator = bb->getTerminator();
        if (auto CI = dyn_cast<BranchInst>(terminator)) {
            assert(CI->isConditional());
            const Value* cond = CI->getCondition();
            exitConds.push_back(cond);
            z3::expr_vector conds = rel2z3(cond, visited, LI, DT, PDT, loops, z3ctx);
            combine_vec(res, conds);
            assert(CI->getNumSuccessors() == 2);
            const BasicBlock* succ = CI->getSuccessor(0);
            true_or_false.push_back(!loop->contains(succ));
        } else {
            errs() << "Unexpected Loop\n";
            exit(0);
        }
    }
    int depth = loop->getLoopDepth();
    std::string N_name = std::string("N") + std::to_string(depth - 1);
    z3::expr N = z3ctx.int_const(N_name.data());
    z3::expr_vector args_in(z3ctx);
    z3::expr_vector args_out(z3ctx);
    z3::sort_vector param(z3ctx);
    for (int j = 0; j < depth - 1; j++) {
        param.push_back(z3ctx.int_sort());
        std::string n_name = std::string("n") + std::to_string(j);
        args_out.push_back(z3ctx.int_const(n_name.data()));
    }
    param.push_back(z3ctx.int_sort());
    args_out.push_back(N);
    std::string last_n_name = std::string("n") + std::to_string(depth - 1);
    args_in.push_back(z3ctx.int_const(last_n_name.data()));

    z3::expr_vector funcs_in_loop(z3ctx);
    z3::expr_vector funcs_out_loop(z3ctx);
    z3::expr final_out_cond(z3ctx.bool_val(false));
    z3::expr final_in_cond(z3ctx.bool_val(true));
    for (int i = 0; i < exitConds.size(); i++) {
        z3::func_decl func = z3ctx.function(exitConds[i]->getName().data(), param, z3ctx.bool_sort());
        // funcs_in_loop.push_back(func(args_in));
        // funcs_out_loop.push_back(func(args_out));
        final_out_cond = final_out_cond || (true_or_false[i] ? func(args_out) : !func(args_out));
        final_in_cond = final_in_cond && !(true_or_false[i] ? func(args_in) : !func(args_in));
    }

    res.push_back(final_out_cond);
    final_in_cond = z3::forall(args_in, z3::implies(args_in.back() < args_out.back() && args_in.back() >= 0, final_in_cond));
    res.push_back(final_in_cond);
    res.push_back(args_out.back() >= 0);
    return res;
}

// z3::expr _path_condition(const BasicBlock* from, const BasicBlock* to, const LoopInfo& LI, z3::context& z3ctx) {
//     SmallVector<const BasicBlock*, 10> children;
//     z3::expr_vector guards(z3ctx);
//     z3::expr res(z3ctx, z3ctx.bool_val(false));
//     Loop* loop = LI.getLoopFor(from);
//     if (from == to) return res;
//     if (loop) {
//         if (loop->is)
//     }
//     if (LI.isLoopHeader(from)) {
//         Loop* loop = LI.getLoopFor(from);
//         if (!loop->contains(to)) {
//             loop->getExitBlocks(children);
//             for (int i = 0; i < children.size(); i++) guards.push_back(z3ctx.bool_val(true));
//         }
//     } else {
//         Loop* loop = LI.getLoopFor(to);
//         BasicBlock* header = nullptr;
//         BasicBlock* entry = &(to->getParent()->getEntryBlock());
//         if (loop) {
//             header = loop->getHeader();
//         } else {
//             header = entry;
//         }
//         Instruction* term = from->getTerminator();
//         if (auto br = dyn_cast<BranchInst>(term)) {
//             if (br->isConditional()) {
//                 const Use& cond = br->getOperandUse(0);
//                 z3::expr cond_z3 = use2z3(cond, LI, z3ctx);
//                 guards.push_back(cond_z3);
//                 guards.push_back(!cond_z3);
//                 children.push_back(term->getSuccessor(0));
//                 children.push_back(term->getSuccessor(1));
//             } else {
//                 assert(term->getNumSuccessors() == 1);
//                 guards.push_back(z3ctx.bool_val(true));
//                 children.push_back(term->getSuccessor(0));
//             }
//         }
//     }
//     for (int i = 0; i < children.size(); i++) {
//         BasicBlock* bb = children[i];
//         z3::expr children_condition = _path_condition(bb, to, LI, z3ctx);
//         res = res || (children_condition && guards[i]);
//     }
//     return res;
// }

z3::expr path_condition(const BasicBlock* bb, const LoopInfo& LI, z3::context& z3ctx) {
    z3::expr res(z3ctx, z3ctx.bool_val(false));
    const BasicBlock* entry = &(bb->getParent()->getEntryBlock());
    if (bb == entry) return z3ctx.bool_val(true);
    for (auto pred_pp = pred_begin(bb); pred_pp != pred_end(bb); pred_pp++) {
        z3::expr cur_expr(z3ctx, z3ctx.bool_val(true));
        const BasicBlock* pred = *pred_pp;
        Loop* loop = LI.getLoopFor(bb);
        if (loop && LI.isLoopHeader(bb) && loop->contains(pred) && loop->isLoopLatch(pred)) continue;
        const Instruction* term = pred->getTerminator();
        const BranchInst* br = dyn_cast<BranchInst>(term);
        if (br->isConditional()) {
            int idx = 0;
            for (idx = 0; idx < term->getNumSuccessors(); idx++) {
                if (bb == term->getSuccessor(idx)) {
                    break;
                }
            }
            cur_expr = use2z3(br->getOperandUse(0), LI, z3ctx);
            if (idx == 1) {
                cur_expr = !cur_expr;
            }
        }
        z3::expr pred_cond = path_condition(pred, LI, z3ctx);
        res = res || (pred_cond && cur_expr);
    }
    return res;
}


void check_assertion(const Use* u, const LoopInfo& LI, const DominatorTree& DT, const PostDominatorTree& PDT) {
    // const Instruction* defInst = dyn_cast<const Instruction>(v);
    z3::context z3ctx;
    z3::solver solver(z3ctx);
    // solver.add(z3ctx.int_const("N0") == z3ctx.int_const("%i") || z3ctx.int_const("%i") < 0);
    // solver.add(z3ctx.int_const("N0") == 0);
    solver.add(!use2z3(*u, LI, z3ctx));
    Value* v = u->get();
    Instruction* user = dyn_cast<Instruction>(u->getUser());
    const BasicBlock* assert_block = user->getParent();
    errs() << path_condition(assert_block, LI, z3ctx).simplify().to_string() << "\n";
    // std::vector<const Value*> visited;
    // std::set<const Loop*> loops;
    // z3::expr_vector all_z3 = rel2z3(v, visited, LI, DT, PDT, loops, z3ctx);
    // solver.add(all_z3);
    // errs() << solver.to_smt2();
    // switch (solver.check()) {
    //     case z3::sat: errs() << "Wrong\n"; break;
    //     case z3::unsat: errs() << "Correct\n"; break;
    //     default: errs() << "Unknown\n"; break;
    // }
}

int main(int argc, char** argv) {
    LLVMContext ctx;
    SMDiagnostic Err;
    std::unique_ptr<Module> mod(parseIRFile(argv[1], Err, ctx));

    PassBuilder PB;
    LoopAnalysisManager LAM;
    FunctionAnalysisManager FAM;
    CGSCCAnalysisManager CGAM;
    ModuleAnalysisManager MAM;

    // Register all the basic analyses with the managers.
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    ModulePassManager MPM;
    MPM.addPass(createModuleToFunctionPassAdaptor(PromotePass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(LCSSAPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(SimplifyCFGPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(LoopSimplifyPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(InstructionNamerPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(AggressiveInstCombinePass()));
    MPM.run(*mod, MAM);


    std::error_code ec;
    raw_fd_ostream output_fd("tmp/tmp.ll", ec);
    mod->print(output_fd, NULL);
    output_fd.close();
    z3::context z3ctx;
    for (auto F = mod->begin(); F != mod->end(); F++) {
        if (F->getName() == "main") {
    //         z3::expr_vector assertions(z3ctx);
            auto &fam = MAM.getResult<FunctionAnalysisManagerModuleProxy>(*mod).getManager();
            LoopInfo &LI = fam.getResult<LoopAnalysis>(*F);
            DominatorTree DT = DominatorTree(*F);
            PostDominatorTree PDT = PostDominatorTree(*F);
    //         // std::vector<BBPath> allPaths = pathsFromEntry2Exit(&F->getEntryBlock(), LI);
            // z3::expr_vector assertions(z3ctx);
            std::vector<const Use*> assertions = collectAllAssertions(*F);
            for (auto a : assertions) {
                check_assertion(a, LI, DT, PDT);
            }
        }
    }
}
