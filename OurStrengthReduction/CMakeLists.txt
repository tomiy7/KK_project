add_llvm_library( LLVMOurStrenghtReduction MODULE BUILDTREE_ONLY
  OurStrenghtReduction.cpp

  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
  )
