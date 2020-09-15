//
// Created by Martin Blicha on 15.09.20.
//

#ifndef OPENSMT_EXPLAINER_H
#define OPENSMT_EXPLAINER_H

#include "EnodeStore.h"

class Explainer {
protected:
    EnodeStore & store;

    Enode const & getEnode(ERef ref) const { return store[ref]; }
    Enode & getEnode(ERef ref) { return store[ref]; }

    //
    // Explanation routines and data
    //
    void     expExplainEdge(ERef v, ERef p);
    void     expExplain           ( );                            // Main routine for explanation
    void     expExplainAlongPath(ERef, ERef);               // Store explanation in explanation
    void     expEnqueueArguments(ERef, ERef);               // Enqueue arguments to be explained
    void     expReRootOn(ERef);                      // Reroot the proof tree on x
    void     expUnion(ERef, ERef);               // Union of x and y in the explanation
    ERef expFind(ERef);                      // Find for the eq classes of the explanation
    ERef expHighestNode(ERef);                      // Returns the node of the eq class of x that is closest to the root of the explanation tree
    ERef expNCA(ERef, ERef);               // Return the nearest common ancestor of x and y
    void     expCleanup           ( );                            // Undoes the effect of expExplain


#if MORE_DEDUCTIONS
    vec< ERef>                  neq_list;
#endif

    vec< ERef >                 exp_pending;                      // Pending explanations
    vec< ERef >                 exp_undo_stack;                   // Keep track of exp_parent merges
    vec< ERef >                 exp_cleanup;                      // List of nodes to be restored
    int                         time_stamp = 0;                   // Need for finding NCA
    vec< PtAsgn >               explanation;                      // Stores explanation

    //
    // Fast duplicates checking. Cannot be nested !
    //
    Map<PTRef,int,PTRefHash>    duplicates;                       // Fast duplicate checking
    int                         dup_count = 0;                    // Current dup token

    inline void initDup ()        { ++dup_count; }
    inline void storeDup(PTRef e) { if (duplicates.has(e)) duplicates[e] = dup_count; else duplicates.insert(e, dup_count); }
    inline bool isDup   (PTRef e) { return !duplicates.has(e) ? false : duplicates[e] == dup_count; }
    inline void doneDup ()        { }

public:
    Explainer(EnodeStore & store) : store(store) {}
    void expStoreExplanation(ERef, ERef, PtAsgn);         // Store the explanation for the merge
    void expRemoveExplanation();                          // Undoes the effect of expStoreExplanation
    void expExplain(ERef, ERef);               // Enqueue equality and explain
    void fillExplanation(vec<PtAsgn> & expl);
};


#endif //OPENSMT_EXPLAINER_H
