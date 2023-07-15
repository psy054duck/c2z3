#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/LoopInfo.h"

#include "IfConversion.h"

using namespace llvm;

// struct IfConversion: PassInfoMixin<IfConversion> {
//   // Main entry point, takes IR unit to run the pass on (&F) and the
//   // corresponding pass manager (to be queried if need be)
//   PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
// 
//     return PreservedAnalyses::none();
//   }
// 
//   // Without isRequired returning true, this pass will be skipped for functions
//   // decorated with the optnone LLVM attribute. Note that clang -O0 decorates
//   // all functions with optnone.
//   static bool isRequired() { return true; }
// };
PreservedAnalyses IfConversionPass::run(Function &F, FunctionAnalysisManager& FAM) {
    IRBuilder<> builder(F.getContext());
    DominatorTree DT(F);
    PostDominatorTree PDT(F);
    LoopInfo LI(DT);

    for (auto &bb : F) {
        bool has_back_edge = false;
        for (auto &phi : bb.phis()) {
            pred_begin(&bb);
            if (phi.getNumIncomingValues() == 2) {
                BasicBlock* curB = phi.getParent();
                BasicBlock* bb0 = phi.getIncomingBlock(0);
                BasicBlock* bb1 = phi.getIncomingBlock(1);
                BasicBlock* domB = DT.findNearestCommonDominator(bb0, bb1);
                if (!PDT.dominates(curB, domB)) continue;
                Instruction* term = domB->getTerminator();
                BranchInst* branch = dyn_cast<BranchInst>(term);
                if (!branch || !branch->isConditional()) continue;
                Value* condV = branch->getCondition();
            }
        }
    }
    return PreservedAnalyses::none();
}

llvm::PassPluginLibraryInfo getIfConversionPluginInfo() {
    return {LLVM_PLUGIN_API_VERSION, "IfConversion", LLVM_VERSION_STRING,
            [](PassBuilder &PB) {
                PB.registerPipelineParsingCallback(
                    [](StringRef Name, FunctionPassManager &FPM,
                    ArrayRef<PassBuilder::PipelineElement>) {
                    if (Name == "if-conversion") {
                        FPM.addPass(IfConversionPass());
                            return true;
                        }
                        return false;
                    });
          }};
}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getIfConversionPluginInfo();
}
