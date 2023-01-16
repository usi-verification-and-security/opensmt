//
// Created by prova on 13.08.19.
//

#include "PScore.h"
#include "PickySMTSolver.h"
#include <cmath>


bool PickyScoreClassic::isAlreadyChecked(Var v) const {
    return (static_cast<unsigned int>(LAexacts[v].getRound()) == latest_round);
}

Lit PickyScoreClassic::getBest() {
    return buf_PBests.getLit();
}

void PickyScoreClassic::setChecked(Var v) {
    LAexacts[v].setRound(latest_round);
}

bool PickyScoreClassic::safeToSkip(Var v, Lit ref) const {
     return LAupperbounds[v].safeToSkip(LAexacts[var(ref)]);
}

double PickyScoreClassic::getSolverScore(const PickySMTSolver *solver) {
    return solver->trail.size();
}

void PickyScoreClassic::updateSolverScore(double &ss, const PickySMTSolver* solver) {
    for (int j = 0; j < solver->trail.size(); j++)
        updateLAUB(solver->trail[j], solver->trail.size());

    ss = solver->trail.size() - ss;
}

const PickyScoreClassic::UBel PickyScoreClassic::UBel_Undef(-1, -1);

void PickyScoreClassic::updatePBest(Var v)
{
    assert(value(v) == l_Undef);
    ExVal& e = LAexacts[v];
    Lit l_v = mkLit(v, e.betterPolarity());
    buf_PBests.insert(l_v, e);
    assert(value(buf_PBests.getLit()) == l_Undef);
}

void PickyScoreClassic::updateLAUB(Lit l, int props)
{
    UBVal& val = LAupperbounds[var(l)];
    if (sign(l))
        val.updateUB_n(UBel(props, latest_round));
    else
        val.updateUB_p(UBel(props, latest_round));
}

void PickyScoreClassic::setLAExact(Var v, int pprops, int nprops)
{
    LAexacts[v] = ExVal(pprops, nprops, latest_round);
}

void PickyScoreClassic::setLAValue(Var v, int pprops, int nprops) {
    setLAExact(v, pprops, nprops);
}



void PickyScoreClassic::newVar() {
    LAupperbounds.push(); // leave space for the var
    LAexacts.push();      // leave space for the var
}

const PickyScoreClassic::ExVal PickyScoreClassic::ExVal::max_val = ExVal(std::numeric_limits<int>::max(), std::numeric_limits<int>::max(), std::numeric_limits<int>::max());

std::string PickyScoreClassic::ExVal::str() const {
    std::ostringstream ss;
    ss << "[" << this->nprops << "," << this->pprops << "," << this->round << "]";
    return ss.str();
}

// safeToSkip: given an exact value e for a variable b, is it safe to
// skip checking my literal's extra value in the lookahead heuristic?
//
bool PickyScoreClassic::UBVal::safeToSkip(const ExVal& e) const {
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

void PickyScoreDeep::newVar() {
    LAexacts.push();      // leave space for the var
}

void PickyScoreDeep::setLAValue(Var v, int p0, int p1) {
    LAexacts[v] = DoubleVal(latest_round, p0+p1+1024*p0*p1);
}

void PickyScoreDeep::updateSolverScore(double &ss, const PickySMTSolver *solver) {
    double new_score = computeScoreFromClauses(solver->clauses, solver) + computeScoreFromClauses(solver->learnts, solver);
    ss = new_score - ss;
}

double PickyScoreDeep::getSolverScore(const PickySMTSolver *solver) {
    if (base_score_round >= 0 && static_cast<unsigned int>(base_score_round) == latest_round) {
        return cached_score;
    }

    double score = computeScoreFromClauses(solver->clauses, solver) + computeScoreFromClauses(solver->learnts, solver);

    base_score_round = latest_round;
    cached_score = score;

    return score;
}

double PickyScoreDeep::computeScoreFromClauses(const vec<CRef> &clauses, const PickySMTSolver *solver) {
    double score = 0;

    const ClauseAllocator &ca = solver->ca;
    for (int i = 0; i < clauses.size(); i++) {
        unsigned nf = 0, nu = 0;
        bool is_taut = false;

        const Clause& c = ca[clauses[i]];
        for (unsigned j = 0; j < c.size(); j++) {
            if (value(c[j]) == l_False) {
                ++nf;
            }
            else if (value(c[j]) == l_True) {
                is_taut = true;
                break;
            }
            else {
                ++nu;
            }
        }
        if (!is_taut && nf > 0) {
            score += pow(0.5, nu);
        }
    }

    return score;
}

bool PickyScoreDeep::safeToSkip(Var v, Lit) const {
    return static_cast<unsigned int>(LAexacts[v].getRound()) == latest_round;
}

void PickyScoreDeep::setChecked(Var v) {
    LAexacts[v].setRound(latest_round);
}

void PickyScoreDeep::updatePBest(Var v) {
    assert(value(v) == l_Undef);
    DoubleVal e = LAexacts[v];
    Lit l_v = mkLit(v, true);
    buf_PBests.insert(l_v, e);
    assert(value(buf_PBests.getLit()) == l_Undef);
}

bool PickyScoreDeep::isAlreadyChecked(Var v) const {
    return (static_cast<unsigned int>(LAexacts[v].getRound()) == latest_round);
}

Lit PickyScoreDeep::getBest() {
    return buf_PBests.getLit();
}

const PickyScoreDeep::DoubleVal PickyScoreDeep::DoubleVal::max_val = DoubleVal(std::numeric_limits<int>::max(), std::numeric_limits<double>::max());


