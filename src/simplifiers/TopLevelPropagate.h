#include "logics/Logic.h"
#include "minisat/mtl/Vec.h"
#include "cnfizers/Cnfizer.h"

#ifndef Simplifiers_TopLevelPropagate_h
#define Simplifiers_TopLevelPropagate_h

// An implementation of union-find algorithm for substituting variables
class TopLevelPropagator {
    class Node {
      public:
        PTRef  tr;
        int    rank;
        Node*  parent;
        Node(PTRef d) : tr(d), rank(0), parent(this) {} // makeSet
    };

    Logic&      logic;
    Cnfizer&    cnfizer;

    Node        n_false;
    Node        n_true;

    Map<PTRef, Node*, PTRefHash, Equal<PTRef> > PTRefToNode;
    Node* find(Node*);
    void merge(Node*, Node*); // union
    bool contains(PTRef x, PTRef y); // term x contains an occurrence of y
  public:
    TopLevelPropagator(Logic& logic, Cnfizer& cnfizer);
    bool insertBindings(PTRef root); // Insert the top level variable
                                     // bindings implied by the formula
                                     // root
    void substitute(PTRef& root);    // Substitute based on the
                                     // previously inserted bindings
};

#endif
