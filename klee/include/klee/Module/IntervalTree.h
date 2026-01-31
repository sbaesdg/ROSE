#ifndef INTERVAL_TREE_H
#define INTERVAL_TREE_H

#include "llvm/Support/raw_ostream.h"
#include <map>

namespace klee {
template <typename T>
struct Interval {
    uint64_t low, high;
    T info;
    Interval(uint64_t l, uint64_t h) : low(l), high(h) {}
    Interval(uint64_t l, uint64_t h, T i) : low(l), high(h), info(i) {}
};

template <typename T>
class IntervalTree {
private:
    template <typename U>
    struct Node {
        Interval<U> interval;
        int64_t max;
        Node<U>* left;
        Node<U>* right;
        int64_t height;
        Node(Interval<U> i) : interval(i), max(i.high), left(nullptr), right(nullptr), height(1) {}
    };
    Node<T>* root;

    Node<T>* copyTree(Node<T>* root) {
        if (!root) return nullptr;
        Node<T>* newRoot = new Node<T>(root->interval);
        newRoot->left = copyTree(root->left);
        newRoot->right = copyTree(root->right);
        newRoot->max = root->max;
        newRoot->height = root->height;
        return newRoot;
    }

    int64_t getHeight(Node<T>* node) {
        return node ? node->height : 0;
    }

    void updateHeight(Node<T>* node) {
        if (node) {
            node->height = 1 + std::max(getHeight(node->left), getHeight(node->right));
        }
    }

    int64_t getBalanceFactor(Node<T>* node) {
        return node ? getHeight(node->left) - getHeight(node->right) : 0;
    }

    void updateMax(Node<T>* node) {
        if (node) {
            node->max = node->interval.high;
            if (node->left) node->max = std::max(node->max, node->left->max);
            if (node->right) node->max = std::max(node->max, node->right->max);
        }
    }

    Node<T>* leftRotate(Node<T>* x) {
        Node<T>* y = x->right;
        Node<T>* t = y->left;
        y->left = x;
        x->right = t;
        updateHeight(x);
        updateHeight(y);
        updateMax(x);
        updateMax(y);
        return y;
    }

    Node<T>* rightRotate(Node<T>* y) {
        Node<T>* x = y->left;
        Node<T>* t = x->right;
        x->right = y;
        y->left = t;
        updateHeight(y);
        updateHeight(x);
        updateMax(y);
        updateMax(x);
        return x;
    }

    Node<T>* insert(Node<T>* root, Interval<T> i) {
        if (!root) return new Node<T>(i);
        if (i.low < root->interval.low) {
            root->left = insert(root->left, i);
        } else {
            root->right = insert(root->right, i);
        }
        updateHeight(root);
        updateMax(root);
        int64_t balance = getBalanceFactor(root);
        if (balance > 1 && i.low < root->left->interval.low) {
            return rightRotate(root);
        }
        if (balance < -1 && i.low >= root->right->interval.low) {
            return leftRotate(root);
        }
        if (balance > 1 && i.low >= root->left->interval.low) {
            root->left = leftRotate(root->left);
            return rightRotate(root);
        }
        if (balance < -1 && i.low < root->right->interval.low) {
            root->right = rightRotate(root->right);
            return leftRotate(root);
        }
        return root;
    }

    Node<T>* getMinNode(Node<T>* root) {
        Node<T>* current = root;
        while (current && current->left) {
            current = current->left;
        }
        return current;
    }

    Node<T>* deleteNode(Node<T>* root, Interval<T> i) {
        if (!root) return root;
        if (i.low < root->interval.low) {
            root->left = deleteNode(root->left, i);
        } else if (i.low > root->interval.low) {
            root->right = deleteNode(root->right, i);
        } else {
            if (!root->left || !root->right) {
                Node<T>* temp = root->left ? root->left : root->right;
                return temp;
            } else {
                Node<T>* temp = getMinNode(root->right);
                root->interval = temp->interval;
                root->right = deleteNode(root->right, temp->interval);
            }
        }
        updateHeight(root);
        updateMax(root);
        int64_t balance = getBalanceFactor(root);
        if (balance > 1 && getBalanceFactor(root->left) >= 0) {
            return rightRotate(root);
        }
        if (balance > 1 && getBalanceFactor(root->left) < 0) {
            root->left = leftRotate(root->left);
            return rightRotate(root);
        }
        if (balance < -1 && getBalanceFactor(root->right) <= 0) {
            return leftRotate(root);
        }
        if (balance < -1 && getBalanceFactor(root->right) > 0) {
            root->right = rightRotate(root->right);
            return leftRotate(root);
        }
        return root;
    }

    void deleteTree(Node<T>* root) {
        if (!root) return;
        deleteTree(root->left);
        deleteTree(root->right);
        delete root;
    }

    bool doOverlap(Interval<T>& i1, Interval<T>& i2) {
        return i1.low <= i2.high && i2.low <= i1.high;
    }

    void searchOverlapping(Node<T>* root, Interval<T>& i, std::vector<Interval<T>*>& result) {
        if (!root) return;
        if (doOverlap(root->interval, i)) {
            result.push_back(&(root->interval));
        }
        if (root->left && root->left->max >= i.low) {
            searchOverlapping(root->left, i, result);
        }
        if (root->right && root->interval.low <= i.high) {
            searchOverlapping(root->right, i, result);
        }
    }

    void printTree(llvm::raw_ostream& out, Node<T>* root, int64_t depth = 0) {
        if (!root) return;
        printTree(out, root->right, depth + 1);
        out.indent(4 * depth) << "[" << root->interval.low << ", " << root->interval.high << "] max = " << root->max << "\n";
        printTree(out, root->left, depth + 1);
    }

public:
    IntervalTree() : root(nullptr) {}

    // copy constructor: deep copy
    IntervalTree(const IntervalTree& other) : root(copyTree(other.root)) {}

    // copy assignment: deep copy
    IntervalTree& operator=(const IntervalTree& other) {
        if (this != &other) {
            deleteTree(root);
            root = copyTree(other.root);
        }
        return *this;
    }

    ~IntervalTree() {
        deleteTree(root);
    }


    void insert(Interval<T> i) {
        root = insert(root, i);
    }

    void remove(Interval<T> i) {
        root = deleteNode(root, i);
    }

    std::vector<Interval<T>*> searchOverlapping(Interval<T>& i) {
        std::vector<Interval<T>*> result;
        searchOverlapping(root, i, result);
        return result;
    }

    int64_t getHeight() {
        return getHeight(root);
    }

    void print(llvm::raw_ostream& out) {
        printTree(out, root);
    }

    void clear() {
        deleteTree(root);
    }
};
}
#endif /* INTERVAL_TREE_H */
