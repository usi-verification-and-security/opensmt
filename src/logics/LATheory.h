//
// Created by Antti on 10.03.21.
//

#ifndef OPENSMT_LATHEORY_H
#define OPENSMT_LATHEORY_H
#include "Theory.h"
#include "ArithmeticEqualityRewriter.h"

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

//
// Unit propagate with simplifications and split equalities into
// inequalities.  If partitions cannot mix, only do the splitting to
// inequalities.
//
template<typename LinAlgLogic, typename LinAlgTSHandler>
bool LATheory<LinAlgLogic,LinAlgTSHandler>::simplify(const vec<PFRef>& formulas, PartitionManager& pmanager, int curr)
{
    auto & currentFrame = pfstore[formulas[curr]];
    if (this->keepPartitions()) {
        vec<PTRef> & flas = currentFrame.formulas;
        ArithmeticEqualityRewriter rewriter(lalogic);
        for (PTRef & fla : flas) {
            PTRef old = fla;
            fla = rewriter.rewrite(old);
            pmanager.transferPartitionMembership(old, fla);
        }
        notOkToPartition = rewriter.getAndClearNotOkToPartition();
        currentFrame.root = getLogic().mkAnd(flas);
    } else {
        PTRef coll_f = getCollateFunction(formulas, curr);
        auto subs_res = computeSubstitutions(coll_f);
        PTRef finalFla = flaFromSubstitutionResult(subs_res);
        getTSolverHandler().setSubstitutions(subs_res.usedSubstitution);
        ArithmeticEqualityRewriter rewriter(lalogic);
        currentFrame.root = rewriter.rewrite(finalFla);
        notOkToPartition = rewriter.getAndClearNotOkToPartition();
    }
    return true;
}

#endif //OPENSMT_LATHEORY_H
