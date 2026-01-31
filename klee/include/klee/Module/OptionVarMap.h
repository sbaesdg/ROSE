#ifndef KLEE_OPTION_VAR_MAP_H
#define KLEE_OPTION_VAR_MAP_H
#include "klee/Module/IntervalTree.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/CommandLine.h"
#include <map>
#include <set>
#include <string>
#include <vector>
#include <iostream>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <unistd.h>
#include <fcntl.h>
#include <cassert>


namespace klee {
extern std::set<std::vector<std::string>> visitedConcreteArgs;
extern std::map<std::string, std::pair<llvm::Value*, std::pair<uint64_t, size_t>>> globalVariables;
extern std::map<llvm::Value*, std::pair<uint64_t, size_t>> globalVariableAddresses;
extern llvm::Module* GlobalTheModule;
extern std::vector<std::string> concreteOptionsOfCurrentState;
extern std::vector<std::vector<std::string>> pendingNewSequences;
extern unsigned int pendingNewSequencesLatestIndex;
extern bool solverSat;
extern bool solverSatEnabled;
extern llvm::cl::opt<unsigned int> ServerPort;

size_t getTypeSize(llvm::Type *type);

struct MetaTaintInfo {
  std::string varName;
  uint64_t address;
  size_t size;
  size_t taintStart; // offset from address
  size_t taintLen;
  MetaTaintInfo(std::string varName, uint64_t address, size_t size, size_t taintStart, size_t taintLen) : varName(varName), address(address), size(size), taintStart(taintStart), taintLen(taintLen) {}
  bool operator<(const MetaTaintInfo& rhs) const {
    // FIXME: generally, address + taintStart should be unique?
    return address + taintStart < rhs.address + rhs.taintStart;
  }
};

struct TaintInfo {
  bool is_tainted;
  std::set<MetaTaintInfo> taints;

  TaintInfo() : is_tainted(false) {}
  TaintInfo(bool is_tainted, std::set<MetaTaintInfo> taints) : is_tainted(is_tainted), taints(taints) {}
  TaintInfo(bool is_tainted, MetaTaintInfo taint) : is_tainted(is_tainted) {
    taints.insert(taint);
  }
  bool isTainted() {
    if (is_tainted) {
      assert(!taints.empty());
    }
    return is_tainted;
  }
  std::set<std::string> getArgs() {
    std::set<std::string> args;
    for (MetaTaintInfo ti : taints) {
      args.insert(ti.varName);
    }
    return args;
  }
  void updateInfo(std::set<std::string> newArgs) {
    assert(false);
  }

  void mergeInfoInPlace(TaintInfo ti) {
    // TODO: if taints intersect?
    taints.insert(ti.taints.begin(), ti.taints.end());
    is_tainted = !taints.empty();
  }

  TaintInfo mergeInfo(TaintInfo ti) {
    std::set<MetaTaintInfo> newTaints = taints;
    newTaints.insert(ti.taints.begin(), ti.taints.end());
    return TaintInfo(!newTaints.empty(), newTaints);
  }

  void print() {
    if (is_tainted) {
      llvm::errs() << " Tainted with args: ";
      for (MetaTaintInfo ti : taints) {
        llvm::errs() << ti.varName << "(" << ti.address << ", " << ti.size << ", " << ti.taintStart << ", " << ti.taintLen << ") ";
      }
    } else {
      llvm::errs() << " Not tainted";
    }
  }
};

struct FunctionTaintInfo {
  std::map<llvm::Value*, TaintInfo> instructionTaint;
  std::string functionName;
  std::map<llvm::Value*, std::pair<uint64_t, size_t>> localVariableAddresses;

  FunctionTaintInfo(std::string functionName) : functionName(functionName) {}
  TaintInfo getTaintInfo(llvm::Value* ki) {
    if (instructionTaint.find(ki) != instructionTaint.end()) {
      return instructionTaint[ki];
    } else {
      assert(false && "Taint info not found");
    }
  }
  std::set<std::string> getArgs(llvm::Value* ki) {
    return getTaintInfo(ki).getArgs();
  }
  void updateTaintInfo(llvm::Value* ki, bool is_tainted) {
    assert(false && "Deprecated");
  }
  void updateTaintInfo(llvm::Value* ki, std::set<std::string> args) {
    assert(false && "Deprecated");
  }

  void updateTaintInfo(llvm::Value* ki, TaintInfo ti) {
    // union of taints
    if (instructionTaint.find(ki) != instructionTaint.end()) {
      TaintInfo& oldTi = instructionTaint[ki];
      oldTi.mergeInfoInPlace(ti);
    } else {
      instructionTaint[ki] = ti;
    }
  }

  void updateLocalVarTaintInfo(llvm::Value* ki, uint64_t addr, size_t size){
    assert(false && "Deprecated");
    // TODO: intervalTree for local variables
    // assert(instructionTaint.find(ki) == instructionTaint.end());
    // instructionTaint[ki] = TaintInfo(true, MetaTaintInfo("", addr, size, 0, size));
  }

  bool isTainted(llvm::Value* ki) {
    if (instructionTaint.find(ki) == instructionTaint.end()) {
      return false;
    }
    return getTaintInfo(ki).isTainted();
  }

  bool hasTaintInfo(llvm::Value* ki) {
    return instructionTaint.find(ki) != instructionTaint.end();
  }

  void addLocalVarAddress(llvm::Value* ki, uint64_t addr, size_t size) {
    assert(localVariableAddresses.find(ki) == localVariableAddresses.end());
    localVariableAddresses[ki] = std::make_pair(addr, size);
  }
};

struct StateTaintInfo {
  std::vector<FunctionTaintInfo> stackTaintMap;
  IntervalTree<TaintInfo> globalTaintTree;

  // StateTaintInfo() : stackTaintMap(), globalTaintTree() {}

  // // copy constructor
  // StateTaintInfo(const StateTaintInfo& other) : stackTaintMap(other.stackTaintMap), globalTaintTree(other.globalTaintTree) {}

  // // copy assignment
  // StateTaintInfo& operator=(const StateTaintInfo& other) {
  //   stackTaintMap = other.stackTaintMap;
  //   globalTaintTree = other.globalTaintTree;
  //   return *this;
  // }

  void setTree(IntervalTree<TaintInfo> &tree) {
    globalTaintTree = tree;
  }

  void print() {
    globalTaintTree.print(llvm::errs());
  }

  size_t stackSize() {
    return stackTaintMap.size();
  }
  size_t stackEmpty() {
    return stackTaintMap.empty();
  }
  bool isTainted(llvm::Value* ki) {
    // first check the current function
    if (!stackEmpty()) {
      FunctionTaintInfo& fti = getCurrentFunctionTaintInfo();
      if (fti.isTainted(ki)) {
        return true;
      }
    }
    // then check global variables
    if (globalVariableAddresses.find(ki) != globalVariableAddresses.end()) {
      uint64_t addr = globalVariableAddresses[ki].first;
      size_t size = globalVariableAddresses[ki].second;
      Interval<TaintInfo> target = Interval<TaintInfo>(addr, addr + size);
      std::vector<Interval<TaintInfo>*> overlap = globalTaintTree.searchOverlapping(target);
      bool tainted = false;
      for (Interval<TaintInfo>* interval : overlap) {
        if (interval->info.isTainted()) {
          tainted = true;
          break;
        }
      }
      return tainted;
    }
    return false;
  }
  TaintInfo getTaintInfo(llvm::Value* ki) {
    // first check the current function
    if (!stackEmpty()) {
      FunctionTaintInfo& fti = getCurrentFunctionTaintInfo();
      if (fti.hasTaintInfo(ki)) {
        return fti.getTaintInfo(ki);
      }
    }
    // then check global variables
    if (globalVariableAddresses.find(ki) != globalVariableAddresses.end()) {
      uint64_t addr = globalVariableAddresses[ki].first;
      size_t size = globalVariableAddresses[ki].second;
      Interval<TaintInfo> target = Interval<TaintInfo>(addr, addr + size);
      std::vector<Interval<TaintInfo>*> overlap = globalTaintTree.searchOverlapping(target);
      TaintInfo res;
      for (Interval<TaintInfo>* interval : overlap) {
        res.mergeInfoInPlace(interval->info);
      }
      return res;
    }
    assert(false && "Taint info not found");
    return TaintInfo();
  }

  TaintInfo getAddressTaintInfo(uint64_t addr, size_t size) {
    bool isGlobal = false;
    TaintInfo res;
    Interval<TaintInfo> target = Interval<TaintInfo>(addr, addr + size);
    std::vector<Interval<TaintInfo>*> overlap = globalTaintTree.searchOverlapping(target);
    for (Interval<TaintInfo>* interval : overlap) {
      res.mergeInfoInPlace(interval->info);
    }
    #ifdef ROSE_DEBUG
    if (res.isTainted()) {
      llvm::errs() << "Address " << addr << " with size " << size << " is tainted: ";
      res.print();
      llvm::errs() << "\n";
    }
    #endif
    return res;
  }

  bool isLocalVarSource(llvm::Value* ki) {
    return false;
  }

  void updateLocalVarTaintInfo(llvm::Value* ki, uint64_t addr, size_t size){
    // assert ki is alloca
    assert(dyn_cast<llvm::Instruction>(ki)->getOpcode() == llvm::Instruction::Alloca && "Not an alloca");
    if (!stackEmpty()) {
      FunctionTaintInfo& fti = getCurrentFunctionTaintInfo();
      // update the local variable address info
      fti.addLocalVarAddress(ki, addr, size);
      if (isLocalVarSource(ki)){
        // fti.updateLocalVarTaintInfo(ki, addr, size);
        assert(ki->getType()->isPointerTy());
        std::string arg = ki->getName().str();
        auto elementType = ki->getType()->getPointerElementType();
        #ifdef ROSE_DEBUG
        llvm::errs() << "Local variable " << arg << " type: ";
        // the type of the element pointed to by ki
        elementType->print(llvm::errs());
        llvm::errs() << "\n";
        #endif
        size_t totalSize = getTypeSize(elementType); // in bytes
        assert(totalSize > 0);
        size_t taintStart = 0;
        size_t taintLen = totalSize;
        // if it is a struct, we need to create MetaTaintInfo for every field
        if (elementType->isStructTy()) {
          llvm::StructType* st = llvm::dyn_cast<llvm::StructType>(elementType);
          for (unsigned i = 0; i < st->getNumElements(); i++) {
            #ifdef ROSE_DEBUG
            llvm::errs() << "Field " << i << " type: ";
            st->getElementType(i)->print(llvm::errs());
            llvm::errs() << " size: " << getTypeSize(st->getElementType(i));
            llvm::errs() << " total size: " << totalSize;
            llvm::errs() << "\n";
            #endif
            llvm::Type* elementType = st->getElementType(i);
            size_t elementSize = getTypeSize(elementType);
            std::set<MetaTaintInfo> taints;
            taints.insert(MetaTaintInfo(arg, addr, totalSize, taintStart, elementSize));
            taintStart += elementSize;
            globalTaintTree.insert(Interval<TaintInfo>(addr + taintStart, addr + taintStart + elementSize, TaintInfo(!taints.empty(), taints)));
          }
          assert(taintStart == totalSize);
        } else {
          std::set<MetaTaintInfo> taints;
          taints.insert(MetaTaintInfo(arg, addr, totalSize, taintStart, taintLen));
          globalTaintTree.insert(Interval<TaintInfo>(addr, addr + totalSize, TaintInfo(!taints.empty(), taints)));
        }
        #ifdef ROSE_DEBUG
        llvm::errs() << "Tainted local variable " << arg << ": ";
        Interval<TaintInfo> target = Interval<TaintInfo>(addr, addr + totalSize);
        std::vector<Interval<TaintInfo>*> overlap = globalTaintTree.searchOverlapping(target);
        for (Interval<TaintInfo>* interval : overlap) {
          interval->info.print();
        }
        llvm::errs() << "\n";
        #endif
      }
    }
  }

  std::set<std::string> getArgs(llvm::Value* ki) {
    return getTaintInfo(ki).getArgs();
  }
  void updateTaintInfo(llvm::Value* ki, TaintInfo ti) {
    if (!stackEmpty()) {
      FunctionTaintInfo& fti = getCurrentFunctionTaintInfo();
      if (fti.hasTaintInfo(ki)) {
        fti.updateTaintInfo(ki, ti);
        return;
      }
    }
    if (globalVariableAddresses.find(ki) != globalVariableAddresses.end()) {
      uint64_t addr = globalVariableAddresses[ki].first;
      size_t size = globalVariableAddresses[ki].second;
      Interval<TaintInfo> target = Interval<TaintInfo>(addr, addr + size);
      std::vector<Interval<TaintInfo>*> overlap = globalTaintTree.searchOverlapping(target);
      for (Interval<TaintInfo>* interval : overlap) {
        interval->info.mergeInfoInPlace(ti);
      }
      return;
    }
    if (!stackEmpty()) {
      FunctionTaintInfo& fti = getCurrentFunctionTaintInfo();
      fti.updateTaintInfo(ki, ti);
    }
    return;
  }

  void updateAddressTaintInfo(uint64_t addr, size_t size, TaintInfo ti) {
    bool isGlobal = false;
    // check existing taints
    Interval<TaintInfo> target = Interval<TaintInfo>(addr, addr + size);
    std::vector<Interval<TaintInfo>*> overlap = globalTaintTree.searchOverlapping(target);
    if (overlap.empty()) {
      globalTaintTree.insert(Interval<TaintInfo>(addr, addr + size, ti));
    } else {
      for (Interval<TaintInfo>* interval : overlap) {
        interval->info.mergeInfoInPlace(ti);
      }
    }
    #ifdef ROSE_DEBUG
    llvm::errs() << "Address " << addr << " with size " << size << " is updated: ";
    ti.print();
    llvm::errs() << "\n";
    #endif
    // assert(false && "Unimplemented if the address is not in global variables");
  }

  void updateGlobalVarTaintInfo(llvm::Value* gv, bool is_tainted, std::string arg) {
    assert(globalVariables.find(arg) != globalVariables.end());
    assert(globalVariables[arg].first == gv);
    // gv is the pointer to the global variable
    assert(gv->getType()->isPointerTy());
    auto elementType = gv->getType()->getPointerElementType();
    uint64_t address = globalVariables[arg].second.first;
    assert(address > 0 && "Invalid address");
    // print the type of the global variable
    #ifdef ROSE_DEBUG
    llvm::errs() << "Global variable " << arg << " type: ";
    // the type of the element pointed to by gv
    elementType->print(llvm::errs());
    llvm::errs() << "\n";
    llvm::errs() << "Address: " << address << "\n";
    #endif
    size_t totalSize = getTypeSize(elementType); // in bytes
    assert(totalSize > 0);
    size_t taintStart = 0;
    size_t taintLen = totalSize;
    // if it is a struct, we need to create MetaTaintInfo for every field

    if (elementType->isStructTy()) {
      llvm::StructType* st = llvm::dyn_cast<llvm::StructType>(elementType);
      for (unsigned i = 0; i < st->getNumElements(); i++) {
        #ifdef ROSE_DEBUG
        llvm::errs() << "Field " << i << " type: ";
        st->getElementType(i)->print(llvm::errs());
        llvm::errs() << " size: " << getTypeSize(st->getElementType(i));
        llvm::errs() << " total size: " << totalSize;
        llvm::errs() << "\n";
        #endif
        llvm::Type* elementType = st->getElementType(i);
        size_t elementSize = getTypeSize(elementType);
        std::set<MetaTaintInfo> taints;
        taints.insert(MetaTaintInfo(arg, address, totalSize, taintStart, elementSize));
        taintStart += elementSize;
        globalTaintTree.insert(Interval<TaintInfo>(address + taintStart, address + taintStart + elementSize, TaintInfo(!taints.empty(), taints)));
      }
      assert(taintStart == totalSize);
    } else {
      #ifdef ROSE_DEBUG
      llvm::errs() << "Chunk " << arg << " size: " << totalSize << " start: " << taintStart << " len: " << taintLen << "\n";
      #endif
      std::set<MetaTaintInfo> taints;
      taints.insert(MetaTaintInfo(arg, address, totalSize, taintStart, taintLen));
      globalTaintTree.insert(Interval<TaintInfo>(address, address + totalSize, TaintInfo(!taints.empty(), taints)));
    }
    #ifdef ROSE_DEBUG
    llvm::errs() << "Tainted global variable " << arg << ": ";
    Interval<TaintInfo> target = Interval<TaintInfo>(address, address + totalSize);
    std::vector<Interval<TaintInfo>*> overlap = globalTaintTree.searchOverlapping(target);
    for (Interval<TaintInfo>* interval : overlap) {
      interval->info.print();
    }
    llvm::errs() << "\n";
    #endif
  }
  FunctionTaintInfo& getCurrentFunctionTaintInfo() {
    if (stackEmpty()) {
      assert(false && "Stack empty");
    }
    return stackTaintMap.back();
  }
  std::string getTopFunctionName() {
    if (stackEmpty()) {
      assert(false && "Stack empty");
    }
    return stackTaintMap.back().functionName;
  }
  void pushTaintStack(std::string functionName) {
    stackTaintMap.push_back(FunctionTaintInfo(functionName));
  }
  void popTaintStack() {
    if (stackEmpty()) {
      assert(false && "Stack empty");
    }
    // clear local variable tainted info
    FunctionTaintInfo& fti = stackTaintMap.back();
    for (auto [ki, p] : fti.localVariableAddresses) {
      uint64_t addr = p.first;
      size_t size = p.second;
      Interval<TaintInfo> target = Interval<TaintInfo>(addr, addr + size);
      std::vector<Interval<TaintInfo>*> overlap = globalTaintTree.searchOverlapping(target);
      for (Interval<TaintInfo>* interval : overlap) {
        // assert interval is covered by [addr, addr + size]
        assert(interval->low >= addr && interval->high <= addr + size);
        Interval<TaintInfo> removeInterval = Interval<TaintInfo>(interval->low, interval->high);
        globalTaintTree.remove(removeInterval);
      }
    }
    stackTaintMap.pop_back();
  }
};

extern int serverSocket;

struct OptionVarMap {
  // static std::map<std::string, llvm::Value*> globalVariables;
  // static void clearGlobalVariables() {
    // globalVariables.clear();
  // }
  // static int serverSocket;
  std::map<std::string, std::string> optionVarMap;
  std::map<std::string, std::string> inversedOptionVarMap;
  OptionVarMap() {
    serverSocket = -1;
    // addOptionVar("-glbs", "global_s");
    // addOptionVar("-a", "argv");
    // addOptionVar("-l", "format");
    // addOptionVar("-f", "print_with_color");
    // addOptionVar("-G", "print_group");
    // addOptionVar("-L", "dereference");
    // addOptionVar("-R", "recursive");
    // addOptionVar("-Z", "print_scontext");
    // addOptionVar("-h", "human_output_opts");
    // addOptionVar("-d", "immediate_dirs");
    // addOptionVar("-f", "print_block_size");
    // addOptionVar("-i", "print_inode");
    // addOptionVar("-r", "sort_reverse");
    // addOptionVar("--group-directories-first", "directories_first");
    // addOptionVar("-h", "file_human_output_opts");
    // addOptionVar("--author", "print_author");
    // addOptionVar("-f", "print_hyperlink");
    // addOptionVar("-n", "numeric_ids");
    // addOptionVar("-p", "indicator_style");
    // addOptionVar("-A", "ignore_mode");
    // addOptionVar("-D", "dired");
    // addOptionVar("-g", "print_owner");
    // addOptionVar("-c", "time_type");
  }

  ~OptionVarMap() {
    if (serverSocket != -1) {
      close(serverSocket);
    }
  }

  static int getSocket() {
    if (serverSocket == -1) {
      serverSocket = socket(AF_INET, SOCK_STREAM, 0);
      if (serverSocket == -1) {
        llvm::errs() << "Error creating socket\n";
        exit(1);
      }
      sockaddr_in server_address;
      server_address.sin_family = AF_INET;
      server_address.sin_port = htons(klee::ServerPort);
      inet_pton(AF_INET, "127.0.0.1", &server_address.sin_addr);
      if (connect(serverSocket, (struct sockaddr *)&server_address,
                  sizeof(server_address)) == -1) {
        llvm::errs() << "Error connecting to server\n";
        exit(1);
      }
    }
    assert(serverSocket != -1);
    return serverSocket;
  }

  void addOptionVar(std::string option, std::string var) {
    optionVarMap[option] = var;
    inversedOptionVarMap[var] = option;
  }
  std::string getVar(std::string option) {
    if (optionVarMap.find(option) != optionVarMap.end()) {
      return optionVarMap[option];
    } else {
      assert(false && "Option not found");
      return "";
    }
  }
  std::string getOption(std::string var) {
    if (inversedOptionVarMap.find(var) != inversedOptionVarMap.end()) {
      return inversedOptionVarMap[var];
    } else {
      assert(false && "Var not found");
      return "";
    }
  }
  std::map<std::string, std::string> mapArgsToOptions(std::set<std::string> args) {
    std::map<std::string, std::string> argOptionMap;
    for (std::string arg : args) {
      if (inversedOptionVarMap.find(arg) != inversedOptionVarMap.end()) {
        argOptionMap[arg] = inversedOptionVarMap[arg];
      } else {
        assert(false && "Arg not found");
      }
    }
    return argOptionMap;
  }
  std::set<std::string> mapTaintInfoToOptions(TaintInfo ti) {
    assert(false && "Deprecated");
    auto args = ti.getArgs();
    std::set<std::string> options;
    for (std::string arg : args) {
      if (inversedOptionVarMap.find(arg) != inversedOptionVarMap.end()) {
        options.insert(inversedOptionVarMap[arg]);
      } else {
        // assert(false && "Arg not found");
      }
    }
    return options;
  }
  std::string serializeVectors(std::vector<std::string> &vector) {
    std::string serialized = "< ";
    for (std::string option : vector) {
      serialized += option + " ";
    }
    serialized += " >";
    return serialized;
  }

  void deserializeSequences(std::string &s, std::vector<std::vector<std::string>> &dest) {
    // [ [ concreteArg1 concreteArg2 ... ] [ concreteArg1 concreteArg2 ... ] ... ]
    assert(s[0] == '[' && s[s.size() - 1] == ']');
    unsigned int new_count = 0;
    for (size_t i = 1; i < s.size() - 1; i++) {
      std::vector<std::string> concreteArgs;
      while (s[i] == ' ') {
        i++;
      }
      if (s[i] == ']') {
        assert (i == s.size() - 1);
        break;
      }
      assert(s[i] == '[');
      i++;
      while (s[i] != ']') {
        while (s[i] == ' ') {
          i++;
        }
        if (s[i] == ']') {
          break;
        }
        size_t j = i;
        while (j < s.size() && s[j] != ' ' && s[j] != ']') {
          j++;
        }
        concreteArgs.push_back(s.substr(i, j - i));
        i = j + 1;
      }
      // unsat case
      if (concreteArgs.size() == 1 && concreteArgs[0] == "UNSAT") {
        i++;
        while (i < s.size() && s[i] == ' ') {
          i++;
        }
        assert (new_count == 0 && "UNSAT should be the only result");
        assert (i == s.size() - 1 && s[i] == ']');
        klee::solverSat = false;
        return;
      }
      dest.push_back(concreteArgs);
      new_count++;
    }
    klee::solverSat = true;
    return;
  }

  std::vector<std::vector<std::string>> dynamicAdjusting(TaintInfo ti, std::vector<std::string> concreteArgs) {
    auto args_set = ti.getArgs();
    std::vector<std::string> args(args_set.begin(), args_set.end());
    std::set<std::string> options;
    // query server
    std::string result;
    int client_socket = getSocket();
    std::string input = "dynamic_adjusting";
    // < arg1, arg2, ... > < concreteArg1, concreteArg2, ... >
    input += " ";
    input += serializeVectors(args);
    input += " ";
    input += serializeVectors(concreteArgs);
    #ifdef ROSE_DEBUG
    llvm::errs() << "Sending to server: " << input << "\n";
    llvm::errs() << "socket: " << client_socket << "\n";
    #endif
    send(client_socket, input.c_str(), input.size(), 0);
    char buf[8192];
    recv(client_socket, buf, 8192, 0);
    result = std::string(buf);
    // parse result
    // [ [ concreteArg1 concreteArg2 ... ] [ concreteArg1 concreteArg2 ... ] ... ]
    std::vector<std::vector<std::string>> newConcreteArgs;
  #ifdef ROSE_DEBUG
    llvm::errs() << "Result received from server: " << result << "\n";
  #endif
    deserializeSequences(result, newConcreteArgs);
    return newConcreteArgs;
  }

  void get_option_var_map_client() {
    std::string result;
    int client_socket = getSocket();
    std::string input = "get_option_var_map";
    #ifdef ROSE_DEBUG
    llvm::errs() << "Sending to server: " << input << "\n";
    llvm::errs() << "socket: " << client_socket << "\n";
    #endif
    send(client_socket, input.c_str(), input.size(), 0);
    char buf[8192];
    recv(client_socket, buf, 8192, 0);
    result = std::string(buf);
  #ifdef ROSE_DEBUG
    llvm::errs() << "Result received from server: " << result << "\n";
  #endif
    assert(result[0] == '{' && result[result.size() - 1] == '}');
    std::string option_var_map = result.substr(1, result.size() - 2);
    std::vector<std::string> option_var_mapList;
    std::string delimiter = ", ";
    size_t pos = 0;
    std::string token;
    while ((pos = option_var_map.find(delimiter)) != std::string::npos) {
      token = option_var_map.substr(0, pos);
      option_var_mapList.push_back(token);
      option_var_map.erase(0, pos + delimiter.length());
    }
    option_var_mapList.push_back(option_var_map);
    for (std::string option_var_map : option_var_mapList) {
      size_t colonPos = option_var_map.find(": ");
      std::string arg = option_var_map.substr(1, colonPos - 2);
      std::string option = option_var_map.substr(colonPos + 3, option_var_map.size() - colonPos - 4);
      #ifdef ROSE_DEBUG
      llvm::errs() << "Adding option var: " << arg << " " << option << "\n";
      #endif
      addOptionVar(arg, option);
    }
  }

  void send_constraint(std::string constraint_path) {
    std::string result;
    int client_socket = getSocket();
    std::string separator = " <SEP> ";
    std::string input = "solve " + constraint_path + separator + serializeVectors(concreteOptionsOfCurrentState);
    #ifdef ROSE_DEBUG
    llvm::errs() << "Sending to server: " << input << "\n";
    llvm::errs() << "socket: " << client_socket << "\n";
    #endif
    send(client_socket, input.c_str(), input.size(), 0);
    char buf[8192];
    recv(client_socket, buf, 8192, 0);
    result = std::string(buf);
    // if result contains "Error", then exit
    if (result.find("Error") != std::string::npos) {
      llvm::errs() << "Error: " << result << "\n";
      exit(1);
    }
    #ifdef ROSE_DEBUG
    llvm::errs() << "Result received from server: " << result << "\n";
    #endif
    // parse result
    // [ [ concreteArg1 concreteArg2 ... ] [ concreteArg1 concreteArg2 ... ] ... ]
    pendingNewSequencesLatestIndex = pendingNewSequences.size();
    deserializeSequences(result, pendingNewSequences);
  }

  void get_symbolic_vars(std::vector<std::vector<std::string>> &symbolic_vars) {
    assert(symbolic_vars.empty());
    std::string result;
    int client_socket = getSocket();
    std::string separator = " <SEP> ";
    std::string input = "symbolic vars";
    // symbolic vars
    #ifdef ROSE_DEBUG
    llvm::errs() << "Sending to server: " << input << "\n";
    llvm::errs() << "socket: " << client_socket << "\n";
    #endif
    send(client_socket, input.c_str(), input.size(), 0);
    char buf[8192];
    recv(client_socket, buf, 8192, 0);
    result = std::string(buf);
    // if result contains "Error", then exit
    if (result.find("Error") != std::string::npos) {
      llvm::errs() << "Error: " << result << "\n";
      exit(1);
    }
    #ifdef ROSE_DEBUG
    llvm::errs() << "Result received from server: " << result << "\n";
    #endif
    deserializeSequences(result, symbolic_vars);
  }

  bool validityCheck(){
    for (auto& [var, option] : inversedOptionVarMap) {
      if (globalVariables.find(var) == globalVariables.end()) {
        return false;
      }
    }
    // save runtime address information
    return true;
  }
  std::map<std::string, llvm::Value*> getTaintedGlobalVars(){
    std::map<std::string, llvm::Value*> taintedGlobalVars;
    for (auto [var, option] : inversedOptionVarMap) {
      if (globalVariables.find(var) != globalVariables.end()) {
        taintedGlobalVars[var] = globalVariables[var].first;
      }
    }
    return taintedGlobalVars;
  }
};
extern OptionVarMap globalOptionVarMap;
extern bool encounterSymbol;
extern bool updateOptions;
extern bool forkNewOptionStates;
extern std::vector<void*> newOptionStates;
extern bool priorityStateSelected;
} // namespace klee
#endif