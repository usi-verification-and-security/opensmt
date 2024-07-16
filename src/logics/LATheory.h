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
#include "Rewritings.h"

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

    virtual PTRef preprocessAfterSubstitutions(PTRef, PreprocessingContext const &) override;
};

namespace {

template<typename TLogic>
PTRef rewriteDivMod(TLogic &, PTRef fla) { return fla; }

template<>
PTRef rewriteDivMod<ArithLogic>(ArithLogic & logic, PTRef fla) {
    // Real logic cannot have div and mod
    return not logic.hasIntegers() ? fla : opensmt::rewriteDivMod(logic, fla);
}

}

template<typename LinAlgLogic, typename LinAlgTSHandler>
PTRef LATheory<LinAlgLogic,LinAlgTSHandler>::preprocessAfterSubstitutions(PTRef fla, PreprocessingContext const &) {
    fla = opensmt::rewriteDistincts(getLogic(), fla);
    fla = rewriteDivMod<LinAlgLogic>(lalogic, fla);
    ArithmeticEqualityRewriter equalityRewriter(lalogic);
    fla = equalityRewriter.rewrite(fla);
    return fla;
}



#endif //OPENSMT_LATHEORY_H
