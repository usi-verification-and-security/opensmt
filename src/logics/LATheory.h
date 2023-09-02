/*
* Copyright (c) 2021-2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
* Copyright (c) 2023, Martin Blicha <martin.blicha@gmail.com>
*
*  SPDX-License-Identifier: MIT
*
*/

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
public:
    LATheory(SMTConfig & c, LinAlgLogic & logic)
            : Theory(c)
            , lalogic(logic)
            , latshandler(c, lalogic)
    { }
    virtual LinAlgLogic&          getLogic() override { return lalogic; }
    virtual const LinAlgLogic&    getLogic() const override { return lalogic; }
    virtual LinAlgTHandler&       getTSolverHandler() override { return latshandler; }

    virtual PTRef simplifyTogether(vec<PTRef> const & assertions, bool isBaseFrame) override;
    virtual vec<PTRef> simplifyIndividually(vec<PTRef> const & assertions, PartitionManager & pmanager, bool isBaseFrame) override;
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


template<typename LinAlgLogic, typename LinAlgTSHandler>
PTRef LATheory<LinAlgLogic,LinAlgTSHandler>::simplifyTogether(const vec<PTRef> & assertions, bool) {
    PTRef frameFormula = getLogic().mkAnd(assertions);
    frameFormula = applySubstitutionBasedSimplificationIfEnabled(frameFormula);
    frameFormula = rewriteDistincts(getLogic(), frameFormula);
    frameFormula = rewriteDivMod<LinAlgLogic>(lalogic, frameFormula);
    ArithmeticEqualityRewriter equalityRewriter(lalogic);
    frameFormula = equalityRewriter.rewrite(frameFormula);
    return frameFormula;
}

template<typename LinAlgLogic, typename LinAlgTSHandler>
vec<PTRef> LATheory<LinAlgLogic,LinAlgTSHandler>::simplifyIndividually(const vec<PTRef> & assertions, PartitionManager & pmanager, bool) {
    ArithmeticEqualityRewriter equalityRewriter(lalogic);
    vec<PTRef> rewrittenAssertions;
    assertions.copyTo(rewrittenAssertions);
    for (PTRef & fla : rewrittenAssertions) {
        PTRef old = fla;
        fla = rewriteDistincts(getLogic(), fla);
        fla = rewriteDivMod<LinAlgLogic>(lalogic, fla);
        fla = equalityRewriter.rewrite(fla);
        pmanager.transferPartitionMembership(old, fla);
    }
    return rewrittenAssertions;

}


#endif //OPENSMT_LATHEORY_H
