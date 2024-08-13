//
// Created by Martin Blicha on 15.09.20.
//

#ifndef OPENSMT_EXPLAINER_H
#define OPENSMT_EXPLAINER_H

#include "EnodeStore.h"
#include "UFInterpolator.h"

#include <memory>

namespace opensmt {

class Explainer {
protected:
    //
    // Fast duplicates checking. Cannot be nested !
    //
    struct DupChecker;
    class DuplicateCheckerData {
        Map<PTRef,int,PTRefHash>    duplicates;                       // Fast duplicate checking
        int                         dup_count = 0;                    // Current dup token
        bool                        free = true;
        friend                      struct DupChecker;
    };

    struct DupChecker {
        DuplicateCheckerData &dc;
        DupChecker(DuplicateCheckerData &dc) : dc(dc) {
            if (!dc.free) {
                throw InternalException(); // "Attempt to re-use DuplicateChecker without releasing"
            }
            dc.free = false;
            if (dc.dup_count < std::numeric_limits<int>::max()) {
                ++dc.dup_count;
            } else {
                dc.duplicates.clear();
                dc.dup_count = 0;
            }
        }
        inline void storeDup(PTRef e) { assert(!dc.free); if (dc.duplicates.has(e)) dc.duplicates[e] = dc.dup_count; else dc.duplicates.insert(e, dc.dup_count); }
        inline bool isDup   (PTRef e) { assert(!dc.free); return !dc.duplicates.has(e) ? false : dc.duplicates[e] == dc.dup_count; }
        ~DupChecker() {
            dc.free = true;
        }
    };

    DuplicateCheckerData dcd;

    EnodeStore & store;

    Enode const & getEnode(ERef ref) const { return store[ref]; }
    Enode & getEnode(ERef ref) { return store[ref]; }

    //
    // Explanation routines and data
    //
    using PendingQueue = vec<opensmt::pair<ERef,ERef>>;
    virtual vec<PtAsgn> explain      (opensmt::pair<ERef,ERef>);        // Main routine for explanation
    virtual PtAsgn  explainEdge      (ERef v, ERef p, PendingQueue &exp_pending, DupChecker& dc);
    void explainAlongPath (ERef, ERef, vec<PtAsgn> &outExplanation, PendingQueue &exp_pending, DupChecker& dc); // Store explanation in explanation
    void enqueueArguments (ERef, ERef, PendingQueue &exp_pending); // Enqueue arguments to be explained
    void reRootOn         (ERef);                     // Reroot the proof tree on x
    void makeUnion        (ERef, ERef);               // Union of x and y in the explanation
    ERef findAndCompress  (ERef);                     // Find for the eq classes of the explanation
    ERef NCA              (ERef, ERef);               // Return the nearest common ancestor of x and y
    void cleanup          ();                         // Undoes the effect of expExplain


#if MORE_DEDUCTIONS
    vec< ERef>                  neq_list;
#endif

    vec<ERef>       exp_undo_stack;                   // Keep track of exp_parent merges
    vec<ERef>       exp_cleanup;                      // List of nodes to be restored
    int             time_stamp = 0;                   // Need for finding NCA

    vec<opensmt::pair<PTRef,PTRef>> congruences;
public:
    Explainer(EnodeStore & store) : store(store) {}
    virtual ~Explainer() = default;

    void                storeExplanation    (ERef, ERef, PtAsgn);        // Store the explanation for the merge
    void                removeExplanation   ();                          // Undoes the effect of storeExplanation
    virtual vec<PtAsgn> explain             (ERef, ERef);                // Return explanation of why the given two terms are equal
    const vec<opensmt::pair<PTRef,PTRef>> &getCongruences() const { return congruences; }
};

class InterpolatingExplainer : public Explainer {
protected:
    std::unique_ptr<CGraph> cgraph;

    virtual PtAsgn explainEdge (ERef, ERef, PendingQueue &exp_pending, DupChecker& dc) override;
public:
    InterpolatingExplainer(EnodeStore & store) : Explainer(store) {}

    virtual vec<PtAsgn> explain     (ERef, ERef) override;
    std::unique_ptr<CGraph> getCGraph() { return std::move(cgraph); }
};

}

#endif //OPENSMT_EXPLAINER_H
