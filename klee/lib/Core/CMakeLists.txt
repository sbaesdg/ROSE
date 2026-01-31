#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_library(kleeCore
  AddressSpace.cpp
  MergeHandler.cpp
  CallPathManager.cpp
  Context.cpp
  CoreStats.cpp
  ExecutionState.cpp
  Executor.cpp
  ExecutorUtil.cpp
  ExternalDispatcher.cpp
  ImpliedValue.cpp
  Memory.cpp
  MemoryManager.cpp
  PTree.cpp
  Searcher.cpp
  SeedInfo.cpp
  SpecialFunctionHandler.cpp
  StatsTracker.cpp
  TimingSolver.cpp
  UserSearcher.cpp
)

target_link_libraries(kleeCore PRIVATE
  kleeBasic
  kleeModule
  kleaverSolver
  kleaverExpr
  kleeSupport
)

# ROSE
target_link_libraries(kleaverSolver PRIVATE
  kleeCore
  kleeBasic
  kleeModule
  kleaverExpr
  kleeSupport
)

llvm_config(kleeCore "${USE_LLVM_SHARED}" core executionengine mcjit native support)
# ROSE
SET(PYTHON_INCLUDE_PATH "/usr/include/python3.6")
SET(PYTHON_LIB_PATH "/usr/lib/python3.6/config-3.6m-x86_64-linux-gnu")
SET(PYTHON_LIB "python3.6m")
target_include_directories(kleeCore PRIVATE ${PYTHON_INCLUDE_PATH})
target_link_directories(kleeCore PRIVATE ${PYTHON_LIB_PATH})
target_link_libraries(kleeCore PRIVATE ${PYTHON_LIB})

target_link_libraries(kleeCore PRIVATE ${SQLite3_LIBRARIES})
target_include_directories(kleeCore PRIVATE ${KLEE_INCLUDE_DIRS} ${LLVM_INCLUDE_DIRS} ${SQLite3_INCLUDE_DIRS})
target_compile_options(kleeCore PRIVATE ${KLEE_COMPONENT_CXX_FLAGS})
target_compile_definitions(kleeCore PRIVATE ${KLEE_COMPONENT_CXX_DEFINES})
