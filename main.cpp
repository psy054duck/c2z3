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
z3::expr value2z3(const Value* v, unsigned depth, z3::context &z3ctx) {
    z3::expr res(z3ctx);
    if (auto CI = dyn_cast<ConstantInt>(v)) {
        if (CI->getBitWidth() == 1) {
            res = z3ctx.bool_val(*CI->getValue().getRawData() != 0);
        } else {
            res = z3ctx.int_val(*CI->getValue().getRawData());
        }
    } else if (auto CI = dyn_cast<ICmpInst>(v)) {
        auto predicate = CI->getPredicate();
        z3::expr op0 = value2z3(CI->getOperand(0), depth, z3ctx);
        z3::expr op1 = value2z3(CI->getOperand(1), depth, z3ctx);
        if (ICmpInst::isLT(predicate)) {
            res = op0 < op1;
        } else if (ICmpInst::isGT(predicate)) {
            res = op0 > op1;
        } else if (ICmpInst::isGE(predicate)) {
            res = op0 >= op1;
        } else if (ICmpInst::isLE(predicate)) {
            res = op0 <= op1;
        } else if (ICmpInst::isEquality(predicate)) {
            res = (op0 == op1);
        }
    } else {
        assert(v->hasName());
        if (dyn_cast<IntegerType>(v->getType())->getBitWidth() == 1) {
            res = z3ctx.bool_const(v->getName().data());
        } else {
            res = z3ctx.int_const(v->getName().data());
        }
    }
    return res;
}

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
            z3::expr cond_z3 = value2z3(cond, z3ctx);
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
        unsigned depth = BB->getloo
        if (opcode == Instruction::Add) {
            z3::expr lhs = z3ctx.int_const(I.getName().data());
            cur_expr = (lhs == (value2z3(operands[0], depth, z3ctx) + value2z3(operands[1], depth, z3ctx)));
            // res = res + I.getName().data() + " == " + value2str(operands[0], is_loop) + " + " + value2str(operands[1], is_loop) + "\n";
        } else if (opcode == Instruction::Sub) {
            z3::expr lhs = z3ctx.int_const(I.getName().data());
            cur_expr = (lhs == (value2z3(operands[0], z3ctx) - value2z3(operands[1], z3ctx)));
        } else if (opcode == Instruction::Select) {
            auto &pred = operands[0];
            if (auto cmpStmt = dyn_cast<ICmpInst>(pred)) {
                // auto predicate = cmpStmt->getPredicate();
                z3::expr op0 = value2z3(cmpStmt->getOperand(0), z3ctx);
                z3::expr op1 = value2z3(cmpStmt->getOperand(1), z3ctx);
                z3::expr predicate = value2z3(pred, z3ctx);
                z3::expr lhs(z3ctx);
                int width = dyn_cast<IntegerType>(operands[1]->getType())->getBitWidth();
                if (width == 1) {
                    lhs = z3ctx.bool_const(I.getName().data());
                } else {
                    lhs = z3ctx.int_const(I.getName().data());
                }
                cur_expr = (lhs == z3::ite(predicate, value2z3(operands[1], z3ctx), value2z3(operands[2], z3ctx)));
            } else {
                abortWithInfo("The first operand of Select is not ICmpInst");
            }
        } else if (opcode == Instruction::ICmp) {
            cur_expr = (z3ctx.bool_const(I.getName().data()) == value2z3(&I, z3ctx));
        } else if (opcode == Instruction::Call) {
            auto callStmt = dyn_cast<CallInst>(&I);
            Function* calledFunction = callStmt->getCalledFunction();
            StringRef funcName = calledFunction->getName();
            if (funcName.endswith("assert")) {
                assert(callStmt->arg_size() == 1);
                assertions.push_back(value2z3(callStmt->getArgOperand(0), z3ctx));
            } else if (funcName.startswith("unknown")) {
                cur_expr = z3ctx.int_const(I.getName().data()) == z3ctx.int_const(funcName.data());
                // res = res + I.getName().data() + " == " + funcName.data() + "\n";
            }
        } else if (opcode == Instruction::PHI) {
            int width = dyn_cast<IntegerType>(operands[1]->getType())->getBitWidth();
            z3::expr lhs(z3ctx);
            if (width == 1) {
                lhs = z3ctx.bool_const(I.getName().data());
            } else {
                lhs = z3ctx.int_const(I.getName().data());
            }
            auto phi = dyn_cast<PHINode>(&I);
            Value* instantiatedValue = phi->getIncomingValueForBlock(parentBB);
            cur_expr = (lhs == value2z3(instantiatedValue, z3ctx));
        }
        expr_list.push_back(cur_expr);
        // res += "\n";
    }
    return expr_list;
}

// std::vector<z3::expr> basicBlockLoop2z3(std::vector<std::vector<const BasicBlock*>> &paths, std::vector<z3::expr*> &assertions) {
//     std::vector<z3::expr> res;
//     for (auto& path : paths) {
//         for (auto& bb : path) {
//             res += basicBlock2z3(*bb, assertions, true);
//         }
//     }
//     return res;
// }

// void function2z3(const BasicBlock* entry, const)

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

z3::expr_vector loopBasicBlock2z3(BasicBlock* bb, BasicBlock* parentBB, z3::expr_vector& assertions, const LoopInfo& LI, z3::context z3ctx) {
    Loop* L = LI.getLoopFor(bb);
    unsigned depth = LI.getLoopDepth(bb);
    basicBlock2z3(bb, parentBB, assertions, z3ctx);
}

z3::expr_vector loop2z3(BasicBlock* loopHeader, const LoopInfo& LI, z3::context z3ctx) {
    Loop* L = LI.getLoopFor(loopHeader);
    BasicBlock* preheader = L->getLoopPreheader();
    assert(preheader != nullptr);
    BasicBlock* latch = L->getLoopLatch();
    std::vector<BBPath> paths = pathsFromHeader2Latch(loopHeader, latch, L);
    z3::expr_vector res(z3ctx);
    for (const BBPath &path : paths) {

    }
    return res;
}

void checkPath(const BBPath& path, const LoopInfo& LI) {
    z3::context z3ctx;
    z3::expr_vector assertions(z3ctx);
    z3::expr_vector axioms(z3ctx);
    BasicBlock* parentBB = nullptr;
    for (auto BB : path) {
        if (LI.isLoopHeader(BB)) {

        } else {
            z3::expr_vector localAxioms = basicBlock2z3(BB, parentBB, assertions, z3ctx);
            for (auto expr : localAxioms) {
                axioms.push_back(expr);
            }
        }
        parentBB = BB;
    }
    if (!assertions.empty()) {
        z3::solver s(z3ctx);
        s.add(axioms);
        s.push();
        for (auto a : assertions) {
            s.add(!a);
        }
        // errs() << s.to_smt2() << "\n";
        switch (s.check()) {
            case z3::sat:   errs() << "Wrong\n";   break;
            case z3::unsat: errs() << "Correct\n"; break;
            default:        errs() << "Unknown\n"; break;
        }
        s.pop();
    }
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
            z3::expr_vector assertions(z3ctx);
            auto &fam = MAM.getResult<FunctionAnalysisManagerModuleProxy>(*mod).getManager();
            LoopInfo &LI = fam.getResult<LoopAnalysis>(*F);
            std::vector<BBPath> allPaths = pathsFromEntry2Exit(&F->getEntryBlock(), LI);
            z3::expr_vector expr_list(z3ctx);
            for (BBPath path : allPaths) {
                errs() << "checking assertions on the path \"";
                for (BasicBlock* bb : path) {
                    errs() << bb->getName() << " ";
                }
                errs() << "\"\n";
                checkPath(path, LI);
            }
            // for (auto &BB : *F) {
                // bool in_loop = false;
                // for (auto& L : LI) {
                //     if (L->contains(&BB)) {
                //         in_loop = true;
                //         break;
                //     }
                // }
                // if (in_loop) continue;
                // z3::expr_vector block_expr_list = basicBlock2z3(BB, nullptr, assertions, z3ctx);
                // for (auto e : block_expr_list) {
                //     errs() << e.to_string() << "\n";
                //     expr_list.push_back(e);
                // }
            // }
            // for (auto& L : LI) {
            //     auto header = L->getHeader();
            //     auto latch = L->getLoopLatch();
            //     auto paths = pathsFromHeader2Latch(header, latch, L);
            //     std::vector<Value*> loop_assertions;
            //     errs() << basicBlockLoop2z3(paths, loop_assertions) << "\n";

            //     // for (auto i : paths) {
            //     //     for (auto j : i) {
            //     //         errs() << j->getName() << ' ';
            //     //     }
            //     //     errs() << "\n";
            //     // }
                // z3::solver s(z3ctx);
                // s.add(expr_list);
                // for (auto asser : assertions) {
                //     errs() << asser.to_string() << "\n";
                //     s.push();
                //     s.add(!(asser));
                //     switch (s.check()) {
                //         case z3::sat: errs() << "wrong\n"; break;
                //         case z3::unsat: errs() << "correct\n"; break;
                //         default: errs() << "unknown\n"; break;
                //     }
                //     s.pop();
                // }
        }
    }
}
