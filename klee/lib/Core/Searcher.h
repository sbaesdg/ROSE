//===-- Searcher.h ----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_SEARCHER_H
#define KLEE_SEARCHER_H

#include "ExecutionState.h"
#include "PTree.h"
#include "klee/ADT/RNG.h"
#include "klee/System/Time.h"
#ifdef ROSE
#include "klee/Module/OptionVarMap.h"
#include "PTree.h"
#endif 

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <map>
#include <queue>
#include <set>
#include <vector>

namespace llvm {
class BasicBlock;
class Function;
class Instruction;
class raw_ostream;
} // namespace llvm

namespace klee {
template <class T, class Comparator> class DiscretePDF;
class ExecutionState;
class Executor;

/// A Searcher implements an exploration strategy for the Executor by selecting
/// states for further exploration using different strategies or heuristics.
class Searcher {
public:
  virtual ~Searcher() = default;

  /// Selects a state for further exploration.
  /// \return The selected state.
  virtual ExecutionState &selectState() = 0;

  /// Notifies searcher about new or deleted states.
  /// \param current The currently selected state for exploration.
  /// \param addedStates The newly branched states with `current` as common
  /// ancestor. \param removedStates The states that will be terminated.
  virtual void update(ExecutionState *current,
                      const std::vector<ExecutionState *> &addedStates,
                      const std::vector<ExecutionState *> &removedStates) = 0;

  /// \return True if no state left for exploration, False otherwise
  virtual bool empty() = 0;

  /// Prints name of searcher as a `klee_message()`.
  // TODO: could probably made prettier or more flexible
  virtual void printName(llvm::raw_ostream &os) = 0;

  enum CoreSearchType : std::uint8_t {
    DFS,
    BFS,
    RandomState,
    RandomPath,
    NURS_CovNew,
    NURS_MD2U,
    NURS_Depth,
    NURS_RP,
    NURS_ICnt,
    NURS_CPICnt,
    NURS_QC
#ifdef ROSE
    ,
    ROSE
#endif
  };
};

/// DFSSearcher implements depth-first exploration. All states are kept in
/// insertion order. The last state is selected for further exploration.
class DFSSearcher final : public Searcher {
  std::vector<ExecutionState *> states;

public:
  ExecutionState &selectState() override;
  void update(ExecutionState *current,
              const std::vector<ExecutionState *> &addedStates,
              const std::vector<ExecutionState *> &removedStates) override;
  bool empty() override;
  void printName(llvm::raw_ostream &os) override;
};

/// BFSSearcher implements breadth-first exploration. When KLEE branches
/// multiple times for a single instruction, all new states have the same depth.
/// Keep in mind that the process tree (PTree) is a binary tree and hence the
/// depth of a state in that tree and its branch depth during BFS are different.
class BFSSearcher final : public Searcher {
  std::deque<ExecutionState *> states;

public:
  ExecutionState &selectState() override;
  void update(ExecutionState *current,
              const std::vector<ExecutionState *> &addedStates,
              const std::vector<ExecutionState *> &removedStates) override;
  bool empty() override;
  void printName(llvm::raw_ostream &os) override;
};

/// RandomSearcher picks a state randomly.
class RandomSearcher final : public Searcher {
  std::vector<ExecutionState *> states;
  RNG &theRNG;

public:
  explicit RandomSearcher(RNG &rng);
  ExecutionState &selectState() override;
  void update(ExecutionState *current,
              const std::vector<ExecutionState *> &addedStates,
              const std::vector<ExecutionState *> &removedStates) override;
  bool empty() override;
  void printName(llvm::raw_ostream &os) override;
};

/// The base class for all weighted searchers. Uses DiscretePDF as underlying
/// data structure.
class WeightedRandomSearcher final : public Searcher {
public:
  enum WeightType : std::uint8_t {
    Depth,
    RP,
    QueryCost,
    InstCount,
    CPInstCount,
    MinDistToUncovered,
    CoveringNew
  };

private:
  std::unique_ptr<DiscretePDF<ExecutionState *, ExecutionStateIDCompare>>
      states;
  RNG &theRNG;
  WeightType type;
  bool updateWeights;

  double getWeight(ExecutionState *);

public:
  /// \param type The WeightType that determines the underlying heuristic.
  /// \param RNG A random number generator.
  WeightedRandomSearcher(WeightType type, RNG &rng);
  ~WeightedRandomSearcher() override = default;

  ExecutionState &selectState() override;
  void update(ExecutionState *current,
              const std::vector<ExecutionState *> &addedStates,
              const std::vector<ExecutionState *> &removedStates) override;
  bool empty() override;
  void printName(llvm::raw_ostream &os) override;
};

/// RandomPathSearcher performs a random walk of the PTree to select a state.
/// PTree is a global data structure, however, a searcher can sometimes only
/// select from a subset of all states (depending on the update calls).
///
/// To support this, RandomPathSearcher has a subgraph view of PTree, in that it
/// only walks the PTreeNodes that it "owns". Ownership is stored in the
/// getInt method of the PTreeNodePtr class (which hides it in the pointer
/// itself).
///
/// The current implementation of PTreeNodePtr supports only 3 instances of the
/// RandomPathSearcher. This is because the current PTreeNodePtr implementation
/// conforms to C++ and only steals the last 3 alignment bits. This restriction
/// could be relaxed slightly by an architecture-specific implementation of
/// PTreeNodePtr that also steals the top bits of the pointer.
///
/// The ownership bits are maintained in the update method.
class RandomPathSearcher final : public Searcher {
  PTree &processTree;
  RNG &theRNG;

  // Unique bitmask of this searcher
  #ifdef ROSE_OPTION_SEARCHER
  const std::bitset<PtrBitCount> idBitMask;
  #else
  const uint8_t idBitMask;
  #endif

public:
  /// \param processTree The process tree.
  /// \param RNG A random number generator.
  RandomPathSearcher(PTree &processTree, RNG &rng);
  ~RandomPathSearcher() override = default;

  ExecutionState &selectState() override;
  void update(ExecutionState *current,
              const std::vector<ExecutionState *> &addedStates,
              const std::vector<ExecutionState *> &removedStates) override;
  bool empty() override;
  void printName(llvm::raw_ostream &os) override;
};

extern llvm::cl::opt<bool> UseIncompleteMerge;
class MergeHandler;
class MergingSearcher final : public Searcher {
  friend class MergeHandler;

private:
  std::unique_ptr<Searcher> baseSearcher;

  /// States that have been paused by the 'pauseState' function
  std::vector<ExecutionState *> pausedStates;

public:
  /// \param baseSearcher The underlying searcher (takes ownership).
  explicit MergingSearcher(Searcher *baseSearcher);
  ~MergingSearcher() override = default;

  /// ExecutionStates currently paused from scheduling because they are
  /// waiting to be merged in a klee_close_merge instruction
  std::set<ExecutionState *> inCloseMerge;

  /// Keeps track of all currently ongoing merges.
  /// An ongoing merge is a set of states (stored in a MergeHandler object)
  /// which branched from a single state which ran into a klee_open_merge(),
  /// and not all states in the set have reached the corresponding
  /// klee_close_merge() yet.
  std::vector<MergeHandler *> mergeGroups;

  /// Remove state from the searcher chain, while keeping it in the executor.
  /// This is used here to 'freeze' a state while it is waiting for other
  /// states in its merge group to reach the same instruction.
  void pauseState(ExecutionState &state);

  /// Continue a paused state
  void continueState(ExecutionState &state);

  ExecutionState &selectState() override;
  void update(ExecutionState *current,
              const std::vector<ExecutionState *> &addedStates,
              const std::vector<ExecutionState *> &removedStates) override;

  bool empty() override;
  void printName(llvm::raw_ostream &os) override;
};

/// BatchingSearcher selects a state from an underlying searcher and returns
/// that state for further exploration for a given time or a given number
/// of instructions.
class BatchingSearcher final : public Searcher {
  std::unique_ptr<Searcher> baseSearcher;
  bool timeBudgetEnabled;
  time::Span timeBudget;
  bool instructionBudgetEnabled;
  unsigned instructionBudget;

  ExecutionState *lastState{nullptr};
  time::Point lastStartTime;
  unsigned lastStartInstructions;

  bool withinTimeBudget() const;
  bool withinInstructionBudget() const;

public:
  /// \param baseSearcher The underlying searcher (takes ownership).
  /// \param timeBudget Time span a state gets selected before choosing a
  /// different one. \param instructionBudget Number of instructions to
  /// re-select a state for.
  BatchingSearcher(Searcher *baseSearcher, time::Span timeBudget,
                   unsigned instructionBudget);
  ~BatchingSearcher() override = default;

  ExecutionState &selectState() override;
  void update(ExecutionState *current,
              const std::vector<ExecutionState *> &addedStates,
              const std::vector<ExecutionState *> &removedStates) override;
  bool empty() override;
  void printName(llvm::raw_ostream &os) override;
};

/// IterativeDeepeningTimeSearcher implements time-based deepening. States
/// are selected from an underlying searcher. When a state reaches its time
/// limit it is paused (removed from underlying searcher). When the underlying
/// searcher runs out of states, the time budget is increased and all paused
/// states are revived (added to underlying searcher).
class IterativeDeepeningTimeSearcher final : public Searcher {
  std::unique_ptr<Searcher> baseSearcher;
  time::Point startTime;
  time::Span time{time::seconds(1)};
  std::set<ExecutionState *> pausedStates;

public:
  /// \param baseSearcher The underlying searcher (takes ownership).
  explicit IterativeDeepeningTimeSearcher(Searcher *baseSearcher);
  ~IterativeDeepeningTimeSearcher() override = default;

  ExecutionState &selectState() override;
  void update(ExecutionState *current,
              const std::vector<ExecutionState *> &addedStates,
              const std::vector<ExecutionState *> &removedStates) override;
  bool empty() override;
  void printName(llvm::raw_ostream &os) override;
};

/// InterleavedSearcher selects states from a set of searchers in round-robin
/// manner. It is used for KLEE's default strategy where it switches between
/// RandomPathSearcher and WeightedRandomSearcher with CoveringNew metric.
class InterleavedSearcher final : public Searcher {
  std::vector<std::unique_ptr<Searcher>> searchers;
  unsigned index{1};

public:
  /// \param searchers The underlying searchers (takes ownership).
  explicit InterleavedSearcher(const std::vector<Searcher *> &searchers);
  ~InterleavedSearcher() override = default;

  ExecutionState &selectState() override;
  void update(ExecutionState *current,
              const std::vector<ExecutionState *> &addedStates,
              const std::vector<ExecutionState *> &removedStates) override;
  bool empty() override;
  void printName(llvm::raw_ostream &os) override;
};

// ROSE
#ifdef ROSE
extern bool considerUpdateCurrent;
class ROSESearcher final : public Searcher {
private:
  std::deque<ExecutionState *> priority_states;
  std::map<ExecutionState *, size_t> state_path_len;
  Searcher *default_searcher;
  #ifdef ROSE_OPTION_SEARCHER
  std::map<std::string, size_t> optionWeights;
  std::map<std::string, Searcher *> optionSearchers;
  #endif
  RNG &theRNG;
  PTree &processTree;

public:
  ROSESearcher(Searcher *ds, RNG &rng, PTree &processTree)
      : default_searcher(ds), theRNG(rng), processTree(processTree) {}
  ~ROSESearcher() {
    priority_states.clear();
    state_path_len.clear();
  }

  ExecutionState &selectState() {
    if (!priority_states.empty()) {
      // pop the first state and return
      auto state = priority_states.front();
      priority_states.pop_front();
      klee::priorityStateSelected = true;
      return *state;
    }
    klee::priorityStateSelected = false;
    #ifdef ROSE_OPTION_SEARCHER
    size_t total_weight = 0;
    for (auto &pair : optionWeights) {
      total_weight += pair.second;
    }
    if (total_weight == 0) {
      return default_searcher->selectState();
    }
    size_t random_weight = theRNG.getInt32() % total_weight;
    std::string selected_option;
    for (auto &pair : optionWeights) {
      if (random_weight < pair.second) {
        selected_option = pair.first;
        break;
      } else {
        random_weight -= pair.second;
      }
    }
    assert(optionSearchers.find(selected_option) != optionSearchers.end());
    Searcher *selected_searcher = optionSearchers[selected_option];
    if (selected_searcher) {
      return selected_searcher->selectState();
    }
    else {
      return default_searcher->selectState();
    }
    #else
    return default_searcher->selectState();
    #endif
  }

  void update(ExecutionState *current,
              const std::vector<ExecutionState *> &addedStates,
              const std::vector<ExecutionState *> &removedStates) {
    if (klee::forkNewOptionStates){
      for (auto state : klee::newOptionStates) {
        priority_states.push_back((ExecutionState *)state);
      }
      klee::newOptionStates.clear();
    }
    if (klee::priorityStateSelected) {
      if (!klee::encounterSymbol && current->steppedInstructions <= current->targetSteppedInstructions) {
        if (std::find(removedStates.begin(), removedStates.end(), current) == removedStates.end()) {
          priority_states.push_back(current);
        }
      }
    }
    default_searcher->update(current, addedStates, removedStates);
    #ifdef ROSE_OPTION_SEARCHER
    for (ExecutionState *state : addedStates) {
      std::vector<std::string> relatedOptions = state->getConcreteArgs();
      for (std::string option : relatedOptions) {
        if (optionWeights.find(option) == optionWeights.end()) {
          optionWeights[option] = 1;
          assert(optionSearchers.find(option) == optionSearchers.end());
          std::vector<Searcher *> defaultSearchers;
          defaultSearchers.push_back(new RandomPathSearcher(processTree, theRNG));
          defaultSearchers.push_back(new WeightedRandomSearcher(WeightedRandomSearcher::CoveringNew, theRNG));
          optionSearchers[option] = new InterleavedSearcher(defaultSearchers);
        } else {
          optionWeights[option] += 1;
        }
        assert (state && "state is nullptr");
        considerUpdateCurrent = false;
        optionSearchers[option]->update(current, {state}, {});
        considerUpdateCurrent = true;
      }
    }
    for (ExecutionState *state : removedStates) {
      std::vector<std::string> relatedOptions = state->getConcreteArgs();
      for (std::string option : relatedOptions) {
        assert(optionWeights.find(option) != optionWeights.end());
        assert(optionWeights[option] > 0);
        assert(optionSearchers.find(option) != optionSearchers.end());
        assert(optionSearchers[option]);
        considerUpdateCurrent = false;
        optionSearchers[option]->update(current, {}, {state});
        considerUpdateCurrent = true;
        optionWeights[option] -= 1;
        if (optionWeights[option] == 0) {
          optionWeights.erase(option);
          delete optionSearchers[option];
          optionSearchers.erase(option);
        }
      }
    }
    assert (considerUpdateCurrent && "considerUpdateCurrent is false");
    #endif
    return;
  }

  bool empty() {
    return default_searcher->empty();
  }

  void printName(llvm::raw_ostream &os) {
    os << "\n*************** ROSESearcher ***************\n";
  }

  void addPriorityState(ExecutionState *state, size_t path_len) {
    priority_states.push_back(state);
    state_path_len[state] = path_len;
  }

};
#endif

} // namespace klee

#endif /* KLEE_SEARCHER_H */
