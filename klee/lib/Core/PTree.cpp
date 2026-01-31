//===-- PTree.cpp ---------------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "PTree.h"

#include "ExecutionState.h"

#include "klee/Expr/Expr.h"
#include "klee/Expr/ExprPPrinter.h"
#include "klee/Support/OptionCategories.h"

#include <bitset>
#include <vector>

using namespace klee;
using namespace llvm;

namespace {

cl::opt<bool>
    CompressProcessTree("compress-process-tree",
                        cl::desc("Remove intermediate nodes in the process "
                                 "tree whenever possible (default=false)"),
                        cl::init(false), cl::cat(MiscCat));

} // namespace

#ifdef ROSE_OPTION_SEARCHER
PTree::PTree(ExecutionState *initialState)
    : root(PTreeNodePtr(new PTreeNode(nullptr, initialState), 0)) {
  initialState->ptreeNode = root.first;
}
#else
PTree::PTree(ExecutionState *initialState)
    : root(PTreeNodePtr(new PTreeNode(nullptr, initialState))) {
  initialState->ptreeNode = root.getPointer();
}
#endif

void PTree::attach(PTreeNode *node, ExecutionState *leftState,
                   ExecutionState *rightState, BranchType reason) {
  #ifdef ROSE_OPTION_SEARCHER
  assert(node && !node->left.first && !node->right.first);
  assert(node == rightState->ptreeNode &&
         "Attach assumes the right state is the current state");
  node->state = nullptr;
  node->left = PTreeNodePtr(new PTreeNode(node, leftState), 0);
  std::bitset<PtrBitCount> currentNodeTag = root.second;
  if (node->parent)
    currentNodeTag = node->parent->left.first == node
                         ? node->parent->left.second
                         : node->parent->right.second;
  node->right = PTreeNodePtr(new PTreeNode(node, rightState), currentNodeTag);
  #else
  assert(node && !node->left.getPointer() && !node->right.getPointer());
  assert(node == rightState->ptreeNode &&
         "Attach assumes the right state is the current state");
  node->state = nullptr;
  node->left = PTreeNodePtr(new PTreeNode(node, leftState));
  uint8_t currentNodeTag = root.getInt();
  if (node->parent)
    currentNodeTag = node->parent->left.getPointer() == node
                         ? node->parent->left.getInt()
                         : node->parent->right.getInt();
  node->right = PTreeNodePtr(new PTreeNode(node, rightState), currentNodeTag);
  #endif
}

void PTree::remove(PTreeNode *n) {
  #ifdef ROSE_OPTION_SEARCHER
  assert(!n->left.first && !n->right.first);
  do {
    PTreeNode *p = n->parent;
    if (p) {
      if (n == p->left.first) {
        p->left = PTreeNodePtr(nullptr, 0);
      } else {
        assert(n == p->right.first);
        p->right = PTreeNodePtr(nullptr, 0);
      }
    }
    if (n->left.first) {
      n->left.first->parent = nullptr;
    }
    if (n->right.first) {
      n->right.first->parent = nullptr;
    }
    delete n;
    n = p;
  } while (n && !n->left.first && !n->right.first);

  if (n && CompressProcessTree) {
    // We're now at a node that has exactly one child; we've just deleted the
    // other one. Eliminate the node and connect its child to the parent
    // directly (if it's not the root).
    PTreeNodePtr child = n->left.first ? n->left : n->right;
    PTreeNode *parent = n->parent;

    child.first->parent = parent;
    if (!parent) {
      // We're at the root.
      root = child;
    } else {
      if (n == parent->left.first) {
        parent->left = child;
      } else {
        assert(n == parent->right.first);
        parent->right = child;
      }
    }

    delete n;
  }
  #else
  assert(!n->left.getPointer() && !n->right.getPointer());
  do {
    PTreeNode *p = n->parent;
    if (p) {
      if (n == p->left.getPointer()) {
        p->left = PTreeNodePtr(nullptr);
      } else {
        assert(n == p->right.getPointer());
        p->right = PTreeNodePtr(nullptr);
      }
    }
    delete n;
    n = p;
  } while (n && !n->left.getPointer() && !n->right.getPointer());

  if (n && CompressProcessTree) {
    // We're now at a node that has exactly one child; we've just deleted the
    // other one. Eliminate the node and connect its child to the parent
    // directly (if it's not the root).
    PTreeNodePtr child = n->left.getPointer() ? n->left : n->right;
    PTreeNode *parent = n->parent;

    child.getPointer()->parent = parent;
    if (!parent) {
      // We're at the root.
      root = child;
    } else {
      if (n == parent->left.getPointer()) {
        parent->left = child;
      } else {
        assert(n == parent->right.getPointer());
        parent->right = child;
      }
    }

    delete n;
  }
  #endif
}

void PTree::dump(llvm::raw_ostream &os) {
  ExprPPrinter *pp = ExprPPrinter::create(os);
  pp->setNewline("\\l");
  os << "digraph G {\n";
  os << "\tsize=\"10,7.5\";\n";
  os << "\tratio=fill;\n";
  os << "\trotate=90;\n";
  os << "\tcenter = \"true\";\n";
  os << "\tnode [style=\"filled\",width=.1,height=.1,fontname=\"Terminus\"]\n";
  os << "\tedge [arrowsize=.3]\n";
  std::vector<const PTreeNode*> stack;
  #ifdef ROSE_OPTION_SEARCHER
  stack.push_back(root.first);
  while (!stack.empty()) {
    const PTreeNode *n = stack.back();
    stack.pop_back();
    os << "\tn" << n << " [shape=diamond";
    if (n->state)
      os << ",fillcolor=green";
    os << "];\n";
    if (n->left.first) {
      os << "\tn" << n << " -> n" << n->left.first;
      os << " [label=0b"
         << std::bitset<PtrBitCount>(n->left.second).to_string() << "];\n";
      stack.push_back(n->left.first);
    }
    if (n->right.first) {
      os << "\tn" << n << " -> n" << n->right.first;
      os << " [label=0b"
         << std::bitset<PtrBitCount>(n->right.second).to_string() << "];\n";
      stack.push_back(n->right.first);
    }
  }
  #else
  stack.push_back(root.getPointer());
  while (!stack.empty()) {
    const PTreeNode *n = stack.back();
    stack.pop_back();
    os << "\tn" << n << " [shape=diamond";
    if (n->state)
      os << ",fillcolor=green";
    os << "];\n";
    if (n->left.getPointer()) {
      os << "\tn" << n << " -> n" << n->left.getPointer();
      os << " [label=0b"
         << std::bitset<PtrBitCount>(n->left.getInt()).to_string() << "];\n";
      stack.push_back(n->left.getPointer());
    }
    if (n->right.getPointer()) {
      os << "\tn" << n << " -> n" << n->right.getPointer();
      os << " [label=0b"
         << std::bitset<PtrBitCount>(n->right.getInt()).to_string() << "];\n";
      stack.push_back(n->right.getPointer());
    }
  }
  #endif
  os << "}\n";
  delete pp;
}

PTreeNode::PTreeNode(PTreeNode *parent, ExecutionState *state) : parent{parent}, state{state} {
  state->ptreeNode = this;
  #ifdef ROSE_OPTION_SEARCHER
  left = PTreeNodePtr(nullptr, 0);
  right = PTreeNodePtr(nullptr, 0);
  #else
  left = PTreeNodePtr(nullptr);
  right = PTreeNodePtr(nullptr);
  #endif
}
