#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/IRBuilder.h"

using namespace llvm;

namespace {
struct OurStrengthReduction : public FunctionPass {
  Value *TrueValue, *FalseValue;
  std::unordered_map<Value *, Value *> VariablesMap;
  std::vector<Instruction *> InstructionsToRemove;
  std::vector<Instruction *> InstructionsToCopy;

  static char ID;
  OurStrengthReduction() : FunctionPass(ID) {}

  bool isConstInt(Value *Operand)
  {
    return isa<ConstantInt>(Operand);
  }

  int getValueFromConstInt(Value *Operand)
  {
    ConstantInt *ConstInt = dyn_cast<ConstantInt>(Operand);
    return ConstInt->getSExtValue();
  }

  bool isPowerOfTwo(int value)
  {
    return (value & std::numeric_limits<int>::max()) == value;
  }

  int powerOfTwo(int value)
  {
    int mask = 1;
    int power = 0;

    while(true) {
      if ((value & mask) == value) {
        return power;
      }
      mask <<= 1;
      power++;
    }
  }

  void mapVariables(Function &F)
  {
    for (BasicBlock &BB : F) {
      for (Instruction &Instr : BB) {
        if (isa<LoadInst>(&Instr)) {
          VariablesMap[&Instr] = Instr.getOperand(0);
        }
      }
    }
  }

  BasicBlock *createTrueBasicBlock(Function *F, Value *Variable)
  {
    BasicBlock *TrueBasicBlock = BasicBlock::Create(F->getContext(), "", F, nullptr);
    IRBuilder<> Builder(TrueBasicBlock->getContext());
    Builder.SetInsertPoint(TrueBasicBlock);
    TrueValue = Builder.CreateLoad(Type::getInt32Ty(TrueBasicBlock->getContext()), VariablesMap[Variable]);
    Builder.CreateBr(&F->back());

    return TrueBasicBlock;
  }

  BasicBlock *createFalseBasicBlock(Function *F, Value *Variable)
  {
    BasicBlock *FalseBasicBlock = BasicBlock::Create(F->getContext(), "", F, nullptr);
    IRBuilder<> Builder(FalseBasicBlock->getContext());
    Builder.SetInsertPoint(FalseBasicBlock);

    Value *TmpVariable = Builder.CreateLoad(Type::getInt32Ty(FalseBasicBlock->getContext()), VariablesMap[Variable]);
    FalseValue = Builder.CreateSub(ConstantInt::get(Type::getInt32Ty(FalseBasicBlock->getContext()), 0), TmpVariable);
    Builder.CreateBr(&F->back());

    return FalseBasicBlock;
  }

  BasicBlock *createUpdateBasicBlock(Function *F, Value *StoreVariable, BasicBlock *TrueBasicBlock, BasicBlock *FalseBasicBlock)
  {
    BasicBlock *UpdateBasicBlock = BasicBlock::Create(F->getContext(), "", F, nullptr);
    IRBuilder<> Builder(UpdateBasicBlock->getContext());
    Builder.SetInsertPoint(UpdateBasicBlock);

    PHINode *PHI = Builder.CreatePHI(Type::getInt32Ty(UpdateBasicBlock->getContext()), 2);
    PHI->addIncoming(TrueValue, TrueBasicBlock);
    PHI->addIncoming(FalseValue, FalseBasicBlock);
    Builder.CreateStore(PHI, StoreVariable);
    Builder.CreateRet(ConstantInt::get(Type::getInt32Ty(UpdateBasicBlock->getContext()), 0));

    for (size_t i = 2; i < InstructionsToCopy.size(); i++) {
      Instruction *Instr = InstructionsToCopy[i]->clone();
      Instr->insertBefore(UpdateBasicBlock->getTerminator());
      InstructionsToCopy[i]->replaceAllUsesWith(Instr);
    }

    InstructionsToRemove.push_back(&UpdateBasicBlock->back());
    return UpdateBasicBlock;
  }

  void removeAllInstructions(BasicBlock &BB, Instruction *CallInstr)
  {
    bool found = false;
    for (Instruction &Instr : BB) {
      if (&Instr == CallInstr) {
        found = true;
      }

      if (found) {
        InstructionsToRemove.push_back(&Instr);
        InstructionsToCopy.push_back(&Instr);
      }
    }
  }

  bool runOnFunction(Function &F) override {
    mapVariables(F);

    for (BasicBlock &BB : F) {
      for (Instruction &Instr : BB) {
        IRBuilder Builder(Instr.getContext());
        if (BinaryOperator *BinaryOp = dyn_cast<BinaryOperator>(&Instr)) {
          Value *LeftOperand = BinaryOp->getOperand(0);
          Value *RightOperand = BinaryOp->getOperand(1);
          if (isa<MulOperator> (&Instr)) {
            if (isConstInt(LeftOperand) && isPowerOfTwo(getValueFromConstInt(LeftOperand)) && !isConstInt(RightOperand)) {
              int power = powerOfTwo(getValueFromConstInt(LeftOperand));
              Instruction *LeftShift = (Instruction *) Builder.CreateShl(RightOperand, power);
              LeftShift->insertAfter(&Instr);
              Instr.replaceAllUsesWith(LeftShift);
              InstructionsToRemove.push_back(&Instr);
            }
            else if (isConstInt(RightOperand) && isPowerOfTwo(getValueFromConstInt(RightOperand)) && !isConstInt(LeftOperand)) {
              int power = powerOfTwo(getValueFromConstInt(RightOperand));
              Instruction *LeftShift = (Instruction *) Builder.CreateShl(LeftOperand, power);
              LeftShift->insertAfter(&Instr);
              Instr.replaceAllUsesWith(LeftShift);
              InstructionsToRemove.push_back(&Instr);
            }
          }
          else if (std::string(Instr.getOpcodeName()) == "srem" && isConstInt(RightOperand) &&
                   !isConstInt(LeftOperand) && isPowerOfTwo(getValueFromConstInt(RightOperand))) {
              Instruction *And = (Instruction *) Builder.CreateAnd(LeftOperand, getValueFromConstInt(RightOperand) - 1);
              And->insertAfter(&Instr);
              Instr.replaceAllUsesWith(And);
              InstructionsToRemove.push_back(&Instr);
          }
        }
        else if (CallInst *Call = dyn_cast<CallInst>(&Instr)) {
          if (Call->getCalledFunction()->getName().str() == "abs") {
            removeAllInstructions(BB, Call);

            Value *VariableToStore;

            if (StoreInst *Store = dyn_cast<StoreInst>(Call->getNextNode())) {
              VariableToStore = Store->getOperand(1);
            }
            else {
              errs() << "Fatal error!\n";
              exit(1);
            }

            Value *Variable = Call->getOperand(0);
            Instruction *ICmp = (Instruction *) Builder.CreateICmpSGE(Variable,
                                                ConstantInt::get(Type::getInt32Ty(Instr.getContext()), 0));
            ICmp->insertAfter(Call);
            BasicBlock *TrueBasicBlock = createTrueBasicBlock(&F, Variable);
            BasicBlock *FalseBasicBlock = createFalseBasicBlock(&F, Variable);
            BasicBlock *UpdateBasicBlock = createUpdateBasicBlock(&F, VariableToStore, TrueBasicBlock, FalseBasicBlock);

            TrueBasicBlock->getTerminator()->setSuccessor(0, UpdateBasicBlock);
            FalseBasicBlock->getTerminator()->setSuccessor(0, UpdateBasicBlock);

            Instruction *Br = (Instruction *) Builder.CreateCondBr(ICmp, TrueBasicBlock, FalseBasicBlock);
            Br->insertAfter(ICmp);
          }
        }
      }
    }

    for (Instruction *Instr : InstructionsToRemove) {
      Instr->eraseFromParent();
    }

    return true;
  }
};
}

char OurStrengthReduction::ID = 0;
static RegisterPass<OurStrengthReduction> X("our-s-r", "Documentation",
                                  false /* Only looks at CFG */,
                                  false /* Analysis Pass */);