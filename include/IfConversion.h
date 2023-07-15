#ifndef IF_CONVERSION_H
#define IF_CONVERSION_H

#include "llvm/IR/PassManager.h"

namespace llvm {

class IfConversionPass: public PassInfoMixin<IfConversionPass> {
public:
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
  static bool isRequired() { return true; }
};

} // namespace llvm

#endif