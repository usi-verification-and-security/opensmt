//
// Created by Antti on 10.03.21.
//

#ifndef OPENSMT_LATHEORY_H
#define OPENSMT_LATHEORY_H
#include "Theory.h"
#include "ArithmeticEqualityRewriter.h"
#include "DistinctRewriter.h"
#include "DivModRewriter.h"

template<typename LinAlgLogic, typename LinAlgTHandler>
class LATheory : public Theory
{
protected:
    LinAlgLogic& lalogic;
    LinAlgTHandler  latshandler;
    std::unique_ptr<Map<PTRef,bool,PTRefHash>> notOkToPartition;
public:
    LATheory(SMTConfig & c, LinAlgLogic & logic)
            : Theory(c)
            , lalogic(logic)
            , latshandler(c, lalogic)
    { }
    ~LATheory() {};
    virtual LinAlgLogic&          getLogic() override { return lalogic; }
    virtual const LinAlgLogic&    getLogic() const override { return lalogic; }
    virtual LinAlgTHandler&       getTSolverHandler() override { return latshandler; }
    virtual bool               simplify(const vec<PFRef>&, PartitionManager& pmanager, int) override; // Theory specific simplifications
    virtual bool               okToPartition(PTRef tr) const override { return !notOkToPartition->has(tr); }
};

namespace {

template<typename TLogic>
PTRef rewriteDivMod(TLogic &, PTRef fla) { return fla; }

template<>
PTRef rewriteDivMod<ArithLogic>(ArithLogic & logic, PTRef fla) {
    // Real logic cannot have div and mod
    return not logic.hasIntegers() ? fla : DivModRewriter(logic).rewrite(fla);
}

}

//
// Unit propagate with simplifications and split equalities into
// inequalities.  If partitions cannot mix, only do the splitting to
// inequalities.
//
template<typename LinAlgLogic, typename LinAlgTSHandler>
bool LATheory<LinAlgLogic,LinAlgTSHandler>::simplify(const vec<PFRef>& formulas, PartitionManager& pmanager, int curr)
{
    auto & currentFrame = pfstore[formulas[curr]];
    ArithmeticEqualityRewriter equalityRewriter(lalogic);
    if (this->keepPartitions()) {
        vec<PTRef> & flas = currentFrame.formulas;
        for (PTRef & fla : flas) {
            PTRef old = fla;
            fla = rewriteDistincts(getLogic(), fla);
            fla = rewriteDivMod<LinAlgLogic>(lalogic, fla);
            fla = equalityRewriter.rewrite(fla);
            pmanager.transferPartitionMembership(old, fla);
        }
        currentFrame.root = getLogic().mkAnd(flas);
    } else {
        PTRef coll_f = getCollateFunction(formulas, curr);
        PTRef finalFla = applySubstitutionBasedSimplificationIfEnabled(coll_f);
        finalFla = rewriteDistincts(getLogic(), finalFla);
        finalFla = rewriteDivMod<LinAlgLogic>(lalogic, finalFla);
        currentFrame.root = equalityRewriter.rewrite(finalFla);
    }
    notOkToPartition = equalityRewriter.getAndClearNotOkToPartition();
    return true;
}

#endif //OPENSMT_LATHEORY_H
