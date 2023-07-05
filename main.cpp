#include "llvm/IRReader/IRReader.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"
#include "llvm/Transforms/Utils/InstructionNamer.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/AggressiveInstCombine/AggressiveInstCombine.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Passes/PassBuilder.h"

#include "z3++.h"

#include <string>
#include <vector>
#include <map>

using namespace llvm;

typedef std::vector<BasicBlock*> BBPath;

void abortWithInfo(const std::string &s) {
    errs() << s << "\n";
    abort();
}

// only works for Use
z3::expr use2z3(const Use* u, const LoopInfo& LI, z3::context &z3ctx) {
    z3::expr res(z3ctx);
    const Value* v = u->get();
    Type* vTy = v->getType();
    assert(vTy->isIntegerTy());
    bool isBoolTy = vTy->isIntegerTy(1);
    if (auto CI = dyn_cast<ConstantInt>(v)) {
        if (isBoolTy) {
            res = z3ctx.bool_val(*CI->getValue().getRawData() != 0);
        } else {
            res = z3ctx.int_val(CI->getSExtValue());
        }
    } else if (auto CI = dyn_cast<ICmpInst>(v)) {
        res = 
        // auto predicate = CI->getPredicate();
        // z3::expr op0 = value2z3(CI->getOperand(0), LI, z3ctx);
        // z3::expr op1 = value2z3(CI->getOperand(1), LI, z3ctx);
        // if (ICmpInst::isLT(predicate)) {
        //     res = op0 < op1;
        // } else if (ICmpInst::isGT(predicate)) {
        //     res = op0 > op1;
        // } else if (ICmpInst::isGE(predicate)) {
        //     res = op0 >= op1;
        // } else if (ICmpInst::isLE(predicate)) {
        //     res = op0 <= op1;
        // } else if (ICmpInst::isEquality(predicate)) {
        //     res = (op0 == op1);
        // }
    }
    if ((!is_used && !isa<ConstantInt>(v)) || res.to_string() == "null") {
        assert(v->hasName());
        auto CI = dyn_cast<Instruction>(v);
        const BasicBlock* parentBB = CI->getParent();
        unsigned depth = LI.getLoopDepth(parentBB);
        z3::sort rangeSort(z3ctx);
        z3::sort domainSort = z3ctx.int_sort();
        z3::sort_vector domainVec(z3ctx);
        if (isBoolTy) {
            rangeSort = z3ctx.bool_sort();
        } else {
            rangeSort = z3ctx.int_sort();
        }
        z3::expr_vector idx_list(z3ctx);
        for (int i = 0; i < depth; i++) {
            domainVec.push_back(domainSort);
            if (is_used) {
                idx_list.push_back(z3ctx.int_const((std::string("n") + std::to_string(i)).c_str()));
            } else {
                idx_list.push_back(z3ctx.int_const((std::string("n") + std::to_string(i)).c_str()) + 1);
            }
        }
        z3::func_decl func_decl = z3ctx.function(v->getName().data(), domainVec, rangeSort);
        res = func_decl(idx_list);
    }
    return res;
}

/*
z3::expr_vector basicBlock2z3(BasicBlock* BB, BasicBlock* parentBB, z3::expr_vector &assertions, z3::context &z3ctx) {
    z3::expr_vector expr_list(z3ctx);
    if (parentBB != nullptr) {
        BranchInst* terminator = dyn_cast<BranchInst>(parentBB->getTerminator());
        if (terminator->isConditional()) {
            int i = 0;
            for (; i < terminator->getNumSuccessors(); i++) {
                if (terminator->getSuccessor(i) == parentBB) {
                    break;
                }
            }
            Value* cond = terminator->getCondition();
            z3::expr cond_z3 = value2z3(cond, 0, z3ctx);
            if (i == 0) {
                expr_list.push_back(cond_z3);
            } else {
                expr_list.push_back(!cond_z3);
            }
        }
    }
    for (auto &I : *BB) {
        auto operands = I.getOperandList();
        auto opcode = I.getOpcode();
        z3::expr cur_expr(z3ctx, z3ctx.bool_val(true));
        unsigned depth = 0;
        if (opcode == Instruction::Add) {
            // errs() << "Add\n";
            z3::expr lhs = z3ctx.int_const(I.getName().data());
            cur_expr = (lhs == (value2z3(operands[0], depth, z3ctx) + value2z3(operands[1], depth, z3ctx)));
        } else if (opcode == Instruction::Sub) {
            // errs() << "Sub\n";
            z3::expr lhs = z3ctx.int_const(I.getName().data());
            cur_expr = (lhs == (value2z3(operands[0], depth, z3ctx) - value2z3(operands[1], depth, z3ctx)));
        } else if (opcode == Instruction::Select) {
            // errs() << "Select\n";
            auto &pred = operands[0];
            if (auto cmpStmt = dyn_cast<ICmpInst>(pred)) {
                z3::expr op0 = value2z3(cmpStmt->getOperand(0), depth, z3ctx);
                z3::expr op1 = value2z3(cmpStmt->getOperand(1), depth, z3ctx);
                z3::expr predicate = value2z3(pred, depth, z3ctx);
                z3::expr lhs(z3ctx);
                int width = dyn_cast<IntegerType>(operands[1]->getType())->getBitWidth();
                if (width == 1) {
                    lhs = z3ctx.bool_const(I.getName().data());
                } else {
                    lhs = z3ctx.int_const(I.getName().data());
                }
                cur_expr = (lhs == z3::ite(predicate, value2z3(operands[1], depth, z3ctx), value2z3(operands[2], depth, z3ctx)));
            } else {
                abortWithInfo("The first operand of Select is not ICmpInst");
            }
        } else if (opcode == Instruction::ICmp) {
            // errs() << "ICmp\n";
            cur_expr = (z3ctx.bool_const(I.getName().data()) == value2z3(&I, depth, z3ctx));
        } else if (opcode == Instruction::Call) {
            auto callStmt = dyn_cast<CallInst>(&I);
            Function* calledFunction = callStmt->getCalledFunction();
            StringRef funcName = calledFunction->getName();
            if (funcName.endswith("assert")) {
                assert(callStmt->arg_size() == 1);
                assertions.push_back(value2z3(callStmt->getArgOperand(0), depth, z3ctx));
            } else if (funcName.startswith("unknown")) {
                cur_expr = z3ctx.int_const(I.getName().data()) == z3ctx.int_const(funcName.data());
            }
        } else if (opcode == Instruction::PHI) {
            // errs() << "PHI\n";
            int width = dyn_cast<IntegerType>(operands[1]->getType())->getBitWidth();
            z3::expr lhs = value2z3(&I, depth, z3ctx, false);
            auto phi = dyn_cast<PHINode>(&I);
            Value* instantiatedValue = phi->getIncomingValueForBlock(parentBB);
            cur_expr = (lhs == value2z3(instantiatedValue, depth, z3ctx));
        }
        z3::expr_vector idx_list(z3ctx);
        z3::expr cond(z3ctx);
        for (int i = 0; i < depth; i++) {
            std::string cur_name = std::string("n") + std::to_string(i);
            z3::expr cur_idx = z3ctx.int_const(cur_name.c_str());
            idx_list.push_back(cur_idx);
            cond = cond && cur_idx >= 0;
        }
        if (depth > 0) {
            expr_list.push_back(z3::forall(idx_list, z3::implies(cond, cur_expr)));
        } else {
            expr_list.push_back(cur_expr);
        }
    }
    return expr_list;
}

void _pathFromHeader2Latch(BasicBlock* cur, BasicBlock* latch, BBPath& cur_v, std::vector<BBPath> &res, const Loop* L) {
    cur_v.push_back(cur);
    if (cur == latch) {
        res.push_back(cur_v);
    } else {
        for (auto cur_bb  : successors(cur)) {
            if (!L->contains(cur_bb)) continue;
            _pathFromHeader2Latch(cur_bb, latch, cur_v, res, L);
        }
    }
    cur_v.pop_back();
}

std::vector<BBPath> pathsFromHeader2Latch(BasicBlock* header, BasicBlock* latch, const Loop* L) {
    std::vector<BBPath> res;
    BBPath cur_v;
    _pathFromHeader2Latch(header, latch, cur_v, res, L);
    return res;
}

void _pathFromEntry2Exit(BasicBlock* cur, BBPath& cur_v, std::vector<BBPath> &res, const LoopInfo &LI) {
    cur_v.push_back(cur);
    if (successors(cur).empty()) {
        res.push_back(cur_v);
    } else if (LI.isLoopHeader(cur)) {
        std::vector<Loop*> allLoops = LI.getTopLevelLoops();
        SmallVector<BasicBlock*> exitBlocks;
        for (const Loop* L : allLoops) {
            if (L->getHeader() == cur) {
                L->getExitBlocks(exitBlocks);
                break;
            }
        }
        for (auto cur_bb : exitBlocks) {
            _pathFromEntry2Exit(cur_bb, cur_v, res, LI);
        }
    } else {
        for (auto cur_bb  : successors(cur)) {
            _pathFromEntry2Exit(cur_bb, cur_v, res, LI);
        }
    }
    cur_v.pop_back();
}

std::vector<BBPath> pathsFromEntry2Exit(BasicBlock* entry, const LoopInfo &LI) {
    std::vector<BBPath> res;
    BBPath cur_v;
    _pathFromEntry2Exit(entry, cur_v, res, LI);
    return res;
}

z3::expr getLoopPathCondition(BasicBlock* bb, Loop* L, z3::context& z3ctx) {
    if (L->getHeader() == bb) {
        return z3ctx.bool_val(true);
    }
    z3::expr res(z3ctx);
    for (auto parentBB : predecessors(bb)) {
        z3::expr cur_expr = getLoopPathCondition(parentBB, L, z3ctx);
        if (!L->isLoopExiting(parentBB)) {
            Instruction* terminator = parentBB->getTerminator();
            BranchInst* br = dyn_cast<BranchInst>(terminator);
            assert(br != nullptr);
            if (br->isConditional()) {
                Value* cond = br->getCondition();
                if (parentBB == br->getSuccessor(0)) {
                    cur_expr = cur_expr && value2z3(cond, L->getLoopDepth(), z3ctx);
                } else {
                    cur_expr = cur_expr && !value2z3(cond, L->getLoopDepth(), z3ctx);
                }
            }
        }
        res = res || cur_expr;
    }
    return res;
}

z3::expr_vector loopBasicBlock2z3(BasicBlock* bb, z3::expr_vector& assertions, const LoopInfo& LI, z3::context& z3ctx) {
    Loop* L = LI.getLoopFor(bb);
    unsigned depth = LI.getLoopDepth(bb);
    z3::expr_vector expr_list(z3ctx);

    errs() << bb->getName() << "\n";
    for (auto &I : *bb) {
        errs() << "\t" << I.getName() << "\n";
        auto operands = I.getOperandList();
        auto opcode = I.getOpcode();
        // z3::expr cur_expr(z3ctx, z3ctx.bool_val(true));
        z3::expr_vector cur_expr_list(z3ctx);
        if (opcode == Instruction::Add) {
            z3::expr lhs = value2z3(&I, depth, z3ctx, false);
            // z3::expr lhs = z3ctx.int_const(I.getName().data());
            cur_expr_list.push_back(lhs == (value2z3(operands[0], depth, z3ctx) + value2z3(operands[1], depth, z3ctx)));
            // res = res + I.getName().data() + " == " + value2str(operands[0], is_loop) + " + " + value2str(operands[1], is_loop) + "\n";
        } else if (opcode == Instruction::Sub) {
            // z3::expr lhs = z3ctx.int_const(I.getName().data());
            z3::expr lhs = value2z3(&I, depth, z3ctx, false);
            cur_expr_list.push_back(lhs == (value2z3(operands[0], depth, z3ctx) - value2z3(operands[1], depth, z3ctx)));
        } else if (opcode == Instruction::Select) {
            auto &pred = operands[0];
            if (auto cmpStmt = dyn_cast<ICmpInst>(pred)) {
                z3::expr op0 = value2z3(cmpStmt->getOperand(0), depth, z3ctx);
                z3::expr op1 = value2z3(cmpStmt->getOperand(1), depth, z3ctx);
                z3::expr predicate = value2z3(pred, depth, z3ctx);
                z3::expr lhs = value2z3(&I, depth, z3ctx, false);
                cur_expr_list.push_back(lhs == z3::ite(predicate, value2z3(operands[1], depth, z3ctx), value2z3(operands[2], depth, z3ctx)));
            } else {
                abortWithInfo("The first operand of Select is not ICmpInst");
            }
        } else if (opcode == Instruction::ICmp) {
            // cur_expr_list.push_back(z3ctx.bool_const(I.getName().data()) == value2z3(&I, depth, z3ctx));
            if (auto cmpStmt = dyn_cast<ICmpInst>(&I)) {
                z3::expr op0 = value2z3(cmpStmt->getOperand(0), depth, z3ctx, true);
                z3::expr op1 = value2z3(cmpStmt->getOperand(1), depth, z3ctx, true);
                z3::expr predicate = value2z3(cmpStmt, depth, z3ctx);
                auto p = cmpStmt->getPredicate();
                if (ICmpInst::isEquality(p)) {
                    cur_expr_list.push_back(predicate == (op0 == op1));
                } else {

                }
            }
        } else if (opcode == Instruction::Call) {
            auto callStmt = dyn_cast<CallInst>(&I);
            Function* calledFunction = callStmt->getCalledFunction();
            StringRef funcName = calledFunction->getName();
            if (funcName.endswith("assert")) {
                assert(callStmt->arg_size() == 1);
                assertions.push_back(value2z3(callStmt->getArgOperand(0), depth, z3ctx));
            } else if (funcName.startswith("unknown")) {
                cur_expr_list.push_back(z3ctx.int_const(I.getName().data()) == z3ctx.int_const(funcName.data()));
            }
        } else if (opcode == Instruction::PHI) {
            z3::expr_vector idx_list(z3ctx);
            z3::expr cond(z3ctx, z3ctx.bool_val(true));
            for (int i = 0; i < depth; i++) {
                std::string cur_name = std::string("n") + std::to_string(i);
                z3::expr cur_idx = z3ctx.int_const(cur_name.c_str());
                idx_list.push_back(cur_idx);
                cond = cond && cur_idx >= 0;
            }
            int width = dyn_cast<IntegerType>(operands[1]->getType())->getBitWidth();
            z3::expr lhs = value2z3(&I, depth, z3ctx, false);
            errs() << "\t\t" << lhs.to_string() << "\n";
            auto phi = dyn_cast<PHINode>(&I);
            // Value* instantiatedValue = phi->getIncomingValueForBlock(parentBB);
            if (L->getHeader() == bb) {
                BasicBlock* preHeader = L->getLoopPreheader();
                BasicBlock* latch = L->getLoopLatch();
                Value* initialValue = phi->getIncomingValueForBlock(preHeader);
                Value* inductiveValue = phi->getIncomingValueForBlock(latch);
                z3::func_decl lhsFuncDecl = lhs.decl();
                unsigned arity = lhsFuncDecl.arity();
                z3::expr_vector idxList(z3ctx);
                for (int i = 0; i < arity; i++) idxList.push_back(z3ctx.int_val(0));
                z3::expr initialLHS = lhsFuncDecl(idxList);
                z3::expr inductiveStmt = (lhs == value2z3(inductiveValue, depth, z3ctx));
                z3::expr initialStmt = (initialLHS == value2z3(initialValue, depth-1, z3ctx));
                cur_expr_list.push_back(initialStmt);
                cur_expr_list.push_back(z3::forall(idx_list, z3::implies(cond, inductiveStmt)));
                errs() << "\t\t" << initialStmt.to_string() << "\n";
                errs() << "\t\t" << inductiveStmt.to_string() << "\n";
            } else {
                auto incomingBlocks = phi->blocks();
                z3::expr_vector conditions(z3ctx);
                z3::expr_vector values(z3ctx);
                for (auto ibb : incomingBlocks) {
                    z3::expr pathCondition = getLoopPathCondition(ibb, L, z3ctx);
                    conditions.push_back(pathCondition);
                    Value* v = phi->getIncomingValueForBlock(ibb);
                    values.push_back(value2z3(v, L->getLoopDepth(), z3ctx));
                }
                z3::expr rhs = values.back();
                for (int i = static_cast<int>(conditions.size()) - 2; i >= 0; i--) {
                    rhs = z3::ite(conditions[i], values[i], rhs);
                }
                // z3::expr test(z3ctx);
                // for (z3::expr e : conditions) {
                    // test = test || e;
                // }
                // errs() << "a phi node\n";
                // errs() << test.to_string() << "\n";
                // z3::expr rhs = value2z3(instantiatedValue, depth, z3ctx);
                // errs() << "\t\t" << rhs.to_string() << "\n";
                
                cur_expr_list.push_back(z3::forall(idx_list, z3::implies(cond, lhs == rhs)));
                // errs() << z3::implies(cond, lhs == rhs).to_string() << "\n";
            }
        }
        for (auto e : cur_expr_list) expr_list.push_back(e);
    }
    return expr_list;
}


z3::expr_vector loop2z3(Loop* L, const LoopInfo& LI, z3::context& z3ctx) {
    // Loop* L = LI.getLoopFor(loopHeader);
    BasicBlock* preheader = L->getLoopPreheader();
    assert(preheader != nullptr);
    BasicBlock* latch = L->getLoopLatch();
    // std::vector<BBPath> paths = pathsFromHeader2Latch(loopHeader, latch, L);
    z3::expr_vector res(z3ctx);
    z3::expr_vector assertions(z3ctx);
    // BasicBlock* parentBB = nullptr;
    auto& allBlocks = L->getBlocksVector();

    for (BasicBlock* BB : allBlocks) {
        z3::expr_vector localAxioms = loopBasicBlock2z3(BB, assertions, LI, z3ctx);
        for (z3::expr e : localAxioms) res.push_back(e);
    }
    z3::expr N = z3ctx.int_const("N");
    res.push_back(N >= 0);
    SmallVector<Loop::Edge> ExitEdges;
    L->getExitEdges(ExitEdges);
    z3::expr exitCondition(z3ctx, z3ctx.bool_val(false));
    for (auto& edge : ExitEdges) {
        Instruction* terminator = edge.first->getTerminator();
        BranchInst* br = dyn_cast<BranchInst>(terminator);
        assert(br->isConditional());
        z3::expr cur_expr(z3ctx);
        if (edge.second == br->getSuccessor(0)) {
            cur_expr = value2z3(br->getCondition(), L->getLoopDepth(), z3ctx);
        } else {
            cur_expr = !value2z3(br->getCondition(), L->getLoopDepth(), z3ctx);
        }
        exitCondition = exitCondition || cur_expr;
    }
    z3::expr n = z3ctx.int_const("n0");
    z3::expr_vector bnd_vars(z3ctx);
    z3::expr_vector N_vars(z3ctx);
    bnd_vars.push_back(n);
    N_vars.push_back(N);
    res.push_back(z3::forall(bnd_vars, z3::implies(n < N && n >= 0, !exitCondition)));
    res.push_back(exitCondition.substitute(bnd_vars, N_vars));
    return res;
}

void checkPath(const BBPath& path, const LoopInfo& LI) {
    z3::context z3ctx;
    z3::expr_vector assertions(z3ctx);
    z3::expr_vector axioms(z3ctx);
    BasicBlock* parentBB = nullptr;
    for (auto BB : path) {
        if (LI.isLoopHeader(BB)) {
            Loop* L = LI.getLoopFor(BB);
            z3::expr_vector localAxioms = loop2z3(L, LI, z3ctx);
            // z3::expr_vector localAxioms = loopBasicBlock2z3(BB, parentBB, assertions, LI, z3ctx);
            for (auto expr : localAxioms) {
                axioms.push_back(expr.simplify());
                // errs() << expr.to_string() << "\n";
            }
            parentBB = nullptr;
        } else {
            z3::expr_vector localAxioms = basicBlock2z3(BB, parentBB, assertions, z3ctx);
            for (auto expr : localAxioms) {
                axioms.push_back(expr.simplify());
            }
            parentBB = BB;
        }
    }
    if (!assertions.empty()) {
        z3::solver s(z3ctx);
        s.add(axioms);
        s.push();
        for (auto a : assertions) {
            s.add(!a);
        }
        errs() << s.to_smt2() << "\n";
        switch (s.check()) {
            case z3::sat:   errs() << "Wrong\n";   break;
            case z3::unsat: errs() << "Correct\n"; break;
            default:        errs() << "Unknown\n"; break;
        }
        s.pop();
    }
}
*/

z3::expr_vector bb2z3(const BasicBlock* bb, z3::expr_vector& assertions, const LoopInfo& LI, z3::context& z3ctx) {
    z3::expr_vector expr_v(z3ctx);
    for (const auto& I : *bb) {
        auto opcode = I.getOpcode();
        z3::expr cur_expr(z3ctx, z3ctx.bool_val(true));
        z3::expr lhs(z3ctx);
        if (I.getType()->isIntegerTy()) {
            if (I.getType()->isIntegerTy(1)) {
                lhs = z3ctx.bool_const(I.getName().data());
            } else {
                lhs = z3ctx.int_const(I.getName().data());
            }
        }
        if (I.isBinaryOp()) {
            z3::expr lhs = z3ctx.int_const(I.getName().data());
            z3::expr operand0 = value2z3(I.getOperandUse(0), LI, z3ctx, true);
            z3::expr operand1 = value2z3(I.getOperandUse(1), LI, z3ctx, true);
            if (opcode == Instruction::Add) {
                cur_expr = (lhs == operand0 + operand1);
            } else if (opcode == Instruction::Sub) {
                cur_expr = (lhs == operand0 - operand1);
            } else if (opcode == Instruction::Mul) {
                cur_expr = (lhs == operand0 * operand1);
            }
        } else if (opcode == Instruction::Select) {
            z3::expr pred = z3ctx.bool_const(I.getOperand(0)->getName().data());
            z3::expr true_v = value2z3(I.getOperand(1), LI, z3ctx, true);
            z3::expr false_v = value2z3(I.getOperand(2), LI, z3ctx, true);
            cur_expr = (lhs == z3::ite(pred, true_v, false_v));
        } else if (opcode == Instruction::ICmp) {
            z3::expr operand0 = value2z3(I.getOperand(0), LI, z3ctx);
            z3::expr operand1 = value2z3(I.getOperand(1), LI, z3ctx);
            if (auto ci = dyn_cast<ICmpInst>(&I)) {
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
        } else if (opcode == Instruction::Call) {
            auto callStmt = dyn_cast<CallInst>(&I);
            Function* calledFunction = callStmt->getCalledFunction();
            StringRef funcName = calledFunction->getName();
            if (funcName.endswith("assert")) {
                assert(callStmt->arg_size() == 1);
                z3::expr ass = z3ctx.bool_const(callStmt->getArgOperand(0)->getName().data());
                assertions.push_back(ass);
            }
        }
        if (!cur_expr.is_true()) {
            expr_v.push_back(cur_expr);
        }
    }
    return expr_v;
}

int main() {
    LLVMContext ctx;
    SMDiagnostic Err;
    std::unique_ptr<Module> mod(parseIRFile("test/test.ll", Err, ctx));

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
    MPM.addPass(createModuleToFunctionPassAdaptor(SimplifyCFGPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(LoopSimplifyPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(InstructionNamerPass()));
    MPM.addPass(createModuleToFunctionPassAdaptor(AggressiveInstCombinePass()));
    MPM.run(*mod, MAM);

    mod->print(errs(), NULL);
    z3::context z3ctx;
    for (auto F = mod->begin(); F != mod->end(); F++) {
        if (F->getName() == "main") {
    //         z3::expr_vector assertions(z3ctx);
            auto &fam = MAM.getResult<FunctionAnalysisManagerModuleProxy>(*mod).getManager();
            LoopInfo &LI = fam.getResult<LoopAnalysis>(*F);
    //         // std::vector<BBPath> allPaths = pathsFromEntry2Exit(&F->getEntryBlock(), LI);
            z3::expr_vector assertions(z3ctx);
            z3::solver solver(z3ctx);
            for (const auto &bb : *F) {
                z3::expr_vector bbz3 = bb2z3(&bb, assertions, LI, z3ctx);
                solver.add(bbz3);
            }
            for (const auto& a : assertions) {
                solver.push();
                solver.add(!a);
                switch (solver.check()) {
                    case z3::sat: errs() << "Wrong\n"; break;
                    case z3::unsat: errs() << "Correct\n"; break;
                    default: errs() << "Unknown\n"; break;
                }
                solver.pop();
            }
            errs() << solver.to_smt2() << "\n";
        }
    }
}
