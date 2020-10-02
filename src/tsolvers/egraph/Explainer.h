//
// Created by Martin Blicha on 15.09.20.
//

#ifndef OPENSMT_EXPLAINER_H
#define OPENSMT_EXPLAINER_H

#include "EnodeStore.h"
#include "UFInterpolator.h"

class Explainer {
protected:
    EnodeStore & store;

    Enode const & getEnode(ERef ref) const { return store[ref]; }
    Enode & getEnode(ERef ref) { return store[ref]; }

    //
    // Explanation routines and data
    //
    virtual void    explain          ();                         // Main routine for explanation
    virtual void    explainEdge      (ERef v, ERef p);
    virtual void    explainAlongPath (ERef, ERef);               // Store explanation in explanation
    virtual void    enqueueArguments (ERef, ERef);               // Enqueue arguments to be explained
    virtual void    reRootOn         (ERef);                     // Reroot the proof tree on x
    virtual void    makeUnion        (ERef, ERef);               // Union of x and y in the explanation
    virtual ERef    find             (ERef);                     // Find for the eq classes of the explanation
    virtual ERef    highestNode      (ERef);                     // Returns the node of the eq class of x that is closest to the root of the explanation tree
    virtual ERef    NCA              (ERef, ERef);               // Return the nearest common ancestor of x and y
    virtual void    cleanup          ();                         // Undoes the effect of expExplain


#if MORE_DEDUCTIONS
    vec< ERef>                  neq_list;
#endif

    vec<ERef>       exp_pending;                      // Pending explanations
    vec<ERef>       exp_undo_stack;                   // Keep track of exp_parent merges
    vec<ERef>       exp_cleanup;                      // List of nodes to be restored
    int             time_stamp = 0;                   // Need for finding NCA
    vec<PtAsgn>     explanation;                      // Stores explanation

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
    virtual ~Explainer() = default;

    void                storeExplanation    (ERef, ERef, PtAsgn);        // Store the explanation for the merge
    void                removeExplanation   ();                          // Undoes the effect of expStoreExplanation
    virtual vec<PtAsgn> explain             (ERef, ERef);                // Return explanation of why the given two terms are equal
};

class InterpolatingExplainer : public Explainer {
protected:
    std::unique_ptr<CGraph> cgraph;

    virtual void        explainEdge (ERef, ERef) override;
public:
    InterpolatingExplainer(EnodeStore & store) : Explainer(store) {}

    virtual vec<PtAsgn> explain     (ERef, ERef) override;
    std::unique_ptr<CGraph> getCGraph() { return std::move(cgraph); }
};

#endif //OPENSMT_EXPLAINER_H
