#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include <unordered_map>
#include <iostream>
#include <set>
#include <llvm/InterfaceStub/IFSStub.h>

#include "llvm/ADT/GenericCycleImpl.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"

using namespace llvm;

namespace {
    struct OurMergeFunctionPass : public FunctionPass {

        std::vector<Function*> FunctionsToDelete;
        std::set<Function*> AlreadyReplaced;
        // std::unordered_map<int, int> ArgumentIndexMapping;
        // std::unordered_map<Value*, Value*> MapVariablesF1;
        // std::unordered_map<Value*, Value*> MapVariablesF2;

        static char ID;
        OurMergeFunctionPass () : FunctionPass(ID) {}

        template<typename Container1, typename Container2>
        auto zip(const Container1& c1, const Container2& c2) {
            std::vector<std::pair<typename Container1::const_iterator, typename Container1::const_iterator>> zipped;

            auto it1 = c1.begin(), it2 = c2.begin();

            while (it1 != c1.end() && it2 != c2.end()) {
                zipped.push_back(std::make_pair(it1, it2));

                ++it1;
                ++it2;
            }

            return zipped;
        }

        bool checkNumberOfConstants(Value* lhs1, Value* rhs1, Value* lhs2, Value* rhs2) {
            int inst1 = 0, inst2 = 0;
            if(isa<Constant>(lhs1))
                inst1++;
            if(isa<Constant>(rhs1))
                inst1++;
            if(isa<Constant>(lhs2))
                inst2++;
            if(isa<Constant>(rhs2))
                inst2++;
            return inst1 == inst2;
        }

        bool checkSyntax(const Function& F1, const Function& F2) {
            auto zipBBs = zip(F1, F2);
            for (auto &[B1, B2] : zipBBs) {

                auto zipInstructions = zip(*B1, *B2);
                for(auto &[I1, I2] : zipInstructions) {

                    if(const auto op1 = dyn_cast<BinaryOperator>(I1)) {
                        if(const auto op2 = dyn_cast<BinaryOperator>(I2)) {
                            if(op1->getOpcode() == op2->getOpcode()) {

                                Value *LHS1 = op1->getOperand(0), *LHS2 = op2->getOperand(0);
                                Value *RHS1 = op1->getOperand(1), *RHS2 = op2->getOperand(1);
                                if(checkNumberOfConstants(LHS1, RHS1, LHS2, RHS2)) {
                                    if(I1->isCommutative() && I2->isCommutative()) {
                                        if(isa<Constant>(LHS1) && isa<Constant>(LHS2) && isa<Constant>(RHS1) && isa<Constant>(RHS2)) {
                                            if(!((LHS1 == LHS2 && RHS1 == RHS2) || (LHS1 == RHS2 && RHS1 == LHS2))) {
                                                return false;
                                            }
                                        }
                                        else if(isa<Constant>(LHS1) && isa<Constant>(LHS2)) {
                                            if(!(LHS1 == LHS2 && RHS1->getType() == RHS2->getType())) {
                                                return false;
                                            }
                                        }
                                        else if(isa<Constant>(RHS1) && isa<Constant>(RHS2)) {
                                            if(!(RHS1 == RHS2 && LHS1->getType() == LHS2->getType())) {
                                                return false;
                                            }
                                        }
                                        else if(isa<Constant>(LHS1) && isa<Constant>(RHS2)) {
                                            if(!(LHS1 == RHS2 && RHS1->getType() == LHS2->getType())) {
                                                return false;
                                            }
                                        }
                                        else if(isa<Constant>(RHS1) && isa<Constant>(LHS2)) {
                                            if(!(RHS1 == LHS2 && LHS1->getType() == RHS2->getType())) {
                                                return false;
                                            }
                                        }
                                        else if(!((LHS1->getType() == LHS2->getType() && RHS1->getType() == RHS2->getType())
                                           || (LHS1->getType() == RHS2->getType() && RHS1->getType() == LHS2->getType()))) {
                                            return false;
                                        }
                                    } else {
                                        if(isa<Constant>(LHS1) && isa<Constant>(LHS2) && isa<Constant>(RHS1) && isa<Constant>(RHS2)) {
                                            if(!(LHS1 == LHS2 && RHS1 == RHS2)) {
                                                return false;
                                            }
                                        }
                                        else if(isa<Constant>(LHS1) && isa<Constant>(LHS2)) {
                                            if(!(LHS1 == LHS2 && RHS1->getType() == RHS2->getType())) {
                                                return false;
                                            }
                                        }
                                        else if(isa<Constant>(RHS1) && isa<Constant>(RHS2)) {
                                            if(!(RHS1 == RHS2 && LHS1->getType() == LHS2->getType())) {
                                                return false;
                                            }
                                        }
                                        else if(!(LHS1->getType() == LHS2->getType() && RHS1->getType() == RHS2->getType())) {
                                            return false;
                                        }
                                    }
                                } else return false;
                            } else return false;
                        } else return false;
                    }
                    if(const auto ret1 = dyn_cast<ReturnInst>(I1)) {
                        if(const auto ret2 = dyn_cast<ReturnInst>(I2)) {
                            const Value* inst1_ret = ret1->getOperand(0);
                            const Value* inst2_ret = ret2->getOperand(0);
                            if(isa<Constant>(ret1->getOperand(0)) && isa<Constant>(ret2->getOperand(0))) {

                                if (inst1_ret == inst2_ret) {
                                    return true;
                                }

                                return false;
                            }
                            if(isa<Constant>(ret1->getOperand(0)))
                                return false;
                            if(isa<Constant>(ret2->getOperand(0)))
                                return false;
                            if(inst1_ret->getType() == inst2_ret->getType())
                                return true;
                        }
                    }
                }
            }
            return true;
        }

        bool equalArguments(const Function& F1, const Function& F2) {
            if(F1.arg_size() != F2.arg_size()) return false;

            if(F1.getReturnType() != F2.getReturnType()) return false;

            std::multiset<Type*> F2_types_set;

            for (const auto& Arg : F2.args()) {
                F2_types_set.insert(Arg.getType());
            }

            for (const auto& Arg : F1.args()) {
                auto it = F2_types_set.find(Arg.getType());

                if(it != F2_types_set.end()) {
                    F2_types_set.erase(it);
                }
            }

            if(!F2_types_set.empty()) {
                return false;
            }

            if (F1.size() != F2.size()) return false;

            if (F1.getInstructionCount() != F2.getInstructionCount()) return false;

            return true;
        }

        // void mapVariablesF1(Function& F) {
        //     for(BasicBlock& BB : F) {
        //         for(Instruction& I : BB) {
        //             if(isa<LoadInst>(&I)) {
        //                 MapVariablesF1[&I] = I.getOperand(0);
        //             }
        //         }
        //     }
        // }
        //
        // void mapVariablesF2(Function& F) {
        //     for(BasicBlock& BB : F) {
        //         for(Instruction& I : BB) {
        //             if(isa<LoadInst>(&I)) {
        //                 MapVariablesF2[&I] = I.getOperand(0);
        //             }
        //         }
        //     }
        // }

        void replaceFunctionCalls(Function& F1, Function& F2) {
            std::vector<Use*> UsesToReplace;
            for(auto& Use : F2.uses()) {
                errs() << "Replacing " << *Use.getUser() << "\n";
                if(dyn_cast<CallInst>(Use.getUser())) {
                    UsesToReplace.push_back(&Use);
                }
            }
            for(auto& Use : UsesToReplace) {
                if(auto *Call = dyn_cast<CallInst>(Use->getUser())) {
                    errs() << "Menjam za " << F2.getName() << "\n";

                    Call->setCalledFunction(&F1);

                }
                //ArgumentIndexMapping.clear();
            }
        }
        //
        // void mapping(const Function& F1, const Function& F2) {
        //     mapVariablesF1(F1);
        //     mapVariablesF2(F2);
        //     auto zipBBs = zip(F1, F2);
        //     for (auto &[B1, B2] : zipBBs) {
        //
        //         auto zipInstructions = zip(*B1, *B2);
        //         for(auto &[I1, I2] : zipInstructions) {
        //
        //             if(const auto op1 = dyn_cast<BinaryOperator>(I1)) {
        //                 if(const auto op2 = dyn_cast<BinaryOperator>(I2)) {
        // }

        bool runOnFunction (Function &F) override {
            errs() << "Processing: " << F.getName() << "\n";
            Module *M = F.getParent();

            for (Function& otherFunc : M->functions()) {
                if (F.isDeclaration()) break;
                if (F.getName().str() == "main" || otherFunc.getName().str() == "main" || otherFunc.isDeclaration()) continue;
                if (&F != &otherFunc && AlreadyReplaced.find(&F) == AlreadyReplaced.end()) {
                    if(otherFunc.use_empty()) {
                        errs() << "Brisace se " << otherFunc.getName() << "\n";
                        FunctionsToDelete.push_back(&otherFunc);
                        AlreadyReplaced.insert(&otherFunc);
                        continue;
                    }
                    if(equalArguments(F, otherFunc)) {
                        if(checkSyntax(F, otherFunc)) {
                            //mapping(F, otherFunc);
                            replaceFunctionCalls(F, otherFunc);
                            FunctionsToDelete.push_back(&otherFunc);
                            AlreadyReplaced.insert(&otherFunc);
                        }
                    }
                }else break;
            }

            for(Function* Func : FunctionsToDelete) {
                Func->eraseFromParent();
            }
            FunctionsToDelete.clear();

            return true;
        }
    };
}

char OurMergeFunctionPass ::ID = 17;
static RegisterPass<OurMergeFunctionPass> X("our-merge-function", "Merge function");

