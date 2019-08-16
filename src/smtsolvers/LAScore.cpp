//
// Created by prova on 13.08.19.
//

#include "LAScore.h"
#include "LookaheadSMTSolver.h"

bool LookaheadScoreClassic::isAlreadyChecked(Var v) const {
    return (LAexacts[v].getRound() == latest_round);
}

Lit LookaheadScoreClassic::getBest() {
    return buf_LABests.getLit();
}

void LookaheadScoreClassic::setChecked(Var v) {
    LAexacts[v].setRound(latest_round);
}

bool LookaheadScoreClassic::safeToSkip(Var v, Lit ref) const {
     return LAupperbounds[v].safeToSkip(LAexacts[var(ref)]);
}

int LookaheadScoreClassic::getSolverScore(const LookaheadSMTSolver *solver) {
    return solver->trail.size();
}

void LookaheadScoreClassic::updateSolverScore(int &ss, const LookaheadSMTSolver* solver) {
    for (int j = 0; j < solver->trail.size(); j++)
        updateLAUB(solver->trail[j], solver->trail.size());

    ss = solver->trail.size() - ss;
}

const LookaheadScoreClassic::UBel LookaheadScoreClassic::UBel_Undef(-1, -1);

void LookaheadScoreClassic::updateLABest(Var v)
{
    assert(value(v) == l_Undef);
    ExVal& e = LAexacts[v];
    Lit l_v = mkLit(v, e.betterPolarity());
    buf_LABests.insert(l_v, e);
    assert(value(buf_LABests.getLit()) == l_Undef);
}

void LookaheadScoreClassic::updateLAUB(Lit l, int props)
{
    UBVal& val = LAupperbounds[var(l)];
    if (sign(l))
        val.updateUB_n(UBel(props, latest_round));
    else
        val.updateUB_p(UBel(props, latest_round));
}

void LookaheadScoreClassic::setLAExact(Var v, int pprops, int nprops)
{
    LAexacts[v] = ExVal(pprops, nprops, latest_round);
}

void LookaheadScoreClassic::setLAValue(Var v, int pprops, int nprops) {
    setLAExact(v, pprops, nprops);
}



void LookaheadScoreClassic::newVar() {
    LAupperbounds.push(); // leave space for the var
    LAexacts.push();      // leave space for the var
}

// safeToSkip: given an exact value e for a variable b, is it safe to
// skip checking my literal's extra value in the lookahead heuristic?
//
bool LookaheadScoreClassic::UBVal::safeToSkip(const ExVal& e) const {
    // My value needs to be current with respect to both polarities and
    // the timestamp of e
    if (!current(e)) return false;

    const UBel &ub_l = getLow();
    const UBel &ub_h = getHigh();

    assert(ub_l != UBel_Undef);

    // If my low-polarity upper bound is less than the low exact of b there is
    // no reason to check me
    if (ub_l.ub < e.getEx_l()) {
        return true;
    }

    // If my low-polarity upper bound is equal to the low exact of b and
    // my high-polarity upper bound is less than or equal to the high
    // exact of b there is no reason to check me
    if (ub_l.ub == e.getEx_l() && ub_h.ub <= e.getEx_h()) {
        return true;
    }

    // In all other cases the value needs to be checked.
    return false;
}
