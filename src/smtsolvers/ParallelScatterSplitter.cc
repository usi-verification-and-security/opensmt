/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */
#include "ParallelScatterSplitter.h"
#include "Proof.h"
#include "SystemQueries.h"
#include "ReportUtils.h"


ParallelScatterSplitter::ParallelScatterSplitter(SMTConfig & c, THandler & t)
    : ScatterSplitter         (c, t)
    , trail_sent            (0)
    , firstPropagation      (true)
{
    syncedStream = nullptr;
    channel = new PTPLib::net::Channel();
}

bool ParallelScatterSplitter::okContinue() const {
    if (channel->shouldStop()) {
        return false;
    } else if (conflicts % 1000 == 0 and splitContext.resourceLimitReached(decisions)) {
        channel->setShouldStop();
        return false;
    } else if (static_cast<int>(splitContext.getCurrentSplitCount()) == splitContext.splitTargetNumber() - 1) {
        channel->setShouldStop();
        return false;
    }
    return true;
}
void ParallelScatterSplitter::notifyEnd() {
    auto [data, result] = ScatterSplitter::createSplitAndBlockAssumptions();
    splitContext.insertSplitData(std::move(data));
    assert(result == l_False);
    (void)result;
    channel->setShouldStop();
}

lbool ParallelScatterSplitter::solve_() {
    lbool result = ScatterSplitter::solve_();
    notifyFoundedResult(result);
    return result;
}

void ParallelScatterSplitter::notifyFoundedResult(lbool const & result) const
{
    if (not channel->isSolverInParallelMode()) return;

    if (result not_eq l_Undef) {
        channel->setShallStop();
        channel->notify_all();
    }
}

lbool ParallelScatterSplitter::zeroLevelConflictHandler() {
    if (splitContext.hasCurrentSplits()) {
        channel->setShouldStop();
        return l_Undef;
    } else {
        return CoreSMTSolver::zeroLevelConflictHandler();
    }
}


CoreSMTSolver::ConsistencyAction ParallelScatterSplitter::notifyConsistency() {
    if (not splitContext.isInSplittingCycle() and splitContext.shouldEnterSplittingCycle(decisions)) {
        splitContext.enterSplittingCycle();
        return ConsistencyAction::BacktrackToZero;
    }
    if (splitContext.isInSplittingCycle() and ScatterSplitter::scatterLevel()) {
        auto [data, result] = createSplitAndBlockAssumptions();
        splitContext.insertSplitData(std::move(data));
        if (result == l_False) { // Rest is unsat
            channel->setShouldStop();
            return ConsistencyAction::ReturnUndef;
        } else {
            splitContext.enterTuningCycle(decisions);
            return ConsistencyAction::SkipToSearchBegin;
        }
    }
    return ConsistencyAction::NoOp;
}

bool ParallelScatterSplitter::learnSomeClauses(std::vector<PTPLib::net::Lemma> & learnedLemmas) {
    int trail_max = this->trail_lim.size() == 0 ? this->trail.size() : this->trail_lim[0];
    trail_sent = std::max<int>(trail_sent, numTriviallyPropagatedOnDl0-1);
    assert(trail_sent >= 0);
    for (int i = this->trail_sent; i < trail_max; i++) {
        this->trail_sent++;
        Lit l = trail[i];
        Var v = var(l);
        if (isAssumptionVar(v)) {
            continue;
        }
        PTRef pt = this->theory_handler.varToTerm(v);
        std::string str = this->theory_handler.getLogic().dumpWithLets(pt);
        assert([&](std::string_view clause_str) {
            if (clause_str.find(".frame") != std::string::npos) {
                throw PTPLib::common::Exception(__FILE__, __LINE__,"assert: frame caught in trail");
            }
            return true;
        }(str));
        pt = sign(l) ? this->theory_handler.getLogic().mkNot(pt) : pt;
        learnedLemmas.emplace_back(PTPLib::net::Lemma(this->theory_handler.getLogic().dumpWithLets(pt), 0));
    }

    for (CRef cr : learnts) {
        Clause &c = this->ca[cr];
        if (c.size() > static_cast<unsigned int>(3 + assumptions.size()) || c.mark() == 3)
            continue;
        int level = 0;
        vec<PTRef> clause;
        bool hasForeignAssumption = false;
        for (unsigned int j = 0; j < c.size(); j++) {
            Lit l = c[j];
            Var v = var(l);
            if (isAssumptionVar(v)) {
                vec<opensmt::pair<int, int>> const & solverBranch_perVar = get_solverBranch(v);
                if (isPrefix(solverBranch_perVar, get_solver_branch())) {
                    int result = solverBranch_perVar.size();
                    assert([&]() {
                        if (result > get_solver_branch().size()) {
                            std::scoped_lock<std::mutex> s_lk(channel->getMutex());
                            throw PTPLib::common::Exception(__FILE__, __LINE__, ";assert: level is greater than solver address length " +
                                channel->get_current_header().at(PTPLib::common::Param.NODE)+ std::to_string(result));
                        }
                        return true;
                    }());

                    assert(result > 0);
                    level = std::max<int>(level, result);
                    continue;
                } else {
                    hasForeignAssumption = true;
                    break;
                }
// Second algorithm of how to correctly publish clauses so that they do not include assumption literals.
// Issue: https://github.com/MasoudAsadzade/OpenSMT2/issues/1
//                int result = getAssumptionLevel(v);
//                if (result >= 1) {
//                    assert(result >= 1);
//                    level = std::max<int>(level, result);
//                    continue;
//                } else {
//                    hasForeignAssumption = true;
//                    break;
//                }
            }
            PTRef pt = theory_handler.varToTerm(v);
            pt = sign(l) ? theory_handler.getLogic().mkNot(pt) : pt;
            clause.push(pt);
        }
        if (hasForeignAssumption or clause.size() > 3)
            continue;
        std::string str = this->theory_handler.getLogic().dumpWithLets(theory_handler.getLogic().mkOr(clause));

        learnedLemmas.emplace_back(PTPLib::net::Lemma(str, level));
        assert([&](std::string_view clause_str) {
            if (clause_str.find(".frame") != std::string::npos) {
                throw PTPLib::common::Exception(__FILE__, __LINE__,";assert: frame caught in actual clauses");
            }
            return true;
        }(str));
        c.mark(3);
    }
    return not learnedLemmas.empty();
}

void ParallelScatterSplitter::set_solver_branch(std::string solver_branch)
{
    solverBranch.clear();
    solver_branch.erase(std::remove(solver_branch.begin(), solver_branch.end(), ' '), solver_branch.end());
    std::string const delimiter{ "," };
    size_t beg, pos = 0;
    uint16_t counter = 0;
    uint16_t temp = 0;
    while ((beg = solver_branch.find_first_not_of(delimiter, pos)) != std::string::npos)
    {
        pos = solver_branch.find_first_of(delimiter, beg + 1);
        int index = stoi(solver_branch.substr(beg, pos - beg));
        if (counter % 2 == 1) {
            solverBranch.push({temp, index});
        } else temp = index;
        counter++;
    }
}

void ParallelScatterSplitter::shallLearnClauses()
{
    if (not channel->isClauseShareMode() and channel->isSolverInParallelMode()) return;

    if (firstPropagation) {
        assert(decisionLevel() == 0);
        firstPropagation = false;
        numTriviallyPropagatedOnDl0 = trail.size();
    }

    std::vector<PTPLib::net::Lemma> toPublishLemmas;
    if (channel->shouldLearnClauses() or not channel->isSolverInParallelMode()) {
        channel->clearShouldLearnClauses();

        if (learnSomeClauses(toPublishLemmas)) {
            {
                std::unique_lock<std::mutex> lk(channel->getMutex());
                if (not lk.owns_lock()) {
                    throw PTPLib::common::Exception(__FILE__, __LINE__,
                                                    ";assert: clause Learning couldn't take the lock");
                }
                channel->insert_learned_clause(std::move(toPublishLemmas));
            }
#ifdef SMTS_ACTIVELOG
            if (syncedStream)
                syncedStream->println(channel->isColorMode() ? PTPLib::common::Color::FG_Green : PTPLib::common::Color::FG_DEFAULT,
                           "[t SEARCH ] -------------- add learned clauses to channel buffer, Size : ", toPublishLemmas.size());
#endif
        }
    }
}

int ParallelScatterSplitter::getAssumptionLevel(Var v) const
{
    assert(isAssumptionVar(v));
    int level = 0;
    for (Lit p : assumptions) {
        if (sign(p)) {
            ++level;
            if (var(p) == v)
                return level;
        }
    }
    return -1;
}

void ParallelScatterSplitter::addBranchToFrameId(opensmt::span<opensmt::pair<int, int> const> && solver_branch, uint32_t fid) {
    vec<opensmt::pair<int,int>> addrVector;
    addrVector.capacity(solver_branch.size());
    for (auto el : solver_branch) {
        addrVector.push(el);
    }
    mapSolverBranchToFrameId(fid, std::move(addrVector));
}