/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */
#include "ScatterSplitter.h"
#include "Random.h"

ScatterSplitter::ScatterSplitter(SMTConfig & c, THandler & t, PTPLib::net::Channel & ch)
: SimpSMTSolver         (c, t)
, Splitter              (c, ch)
{}

bool ScatterSplitter::branchLitRandom() {
    return ((not splitContext.isInSplittingCycle() and opensmt::drand(random_seed) < random_var_freq) or
            (splitContext.isInSplittingCycle() and splitContext.preferRandom()))
           and not order_heap.empty();
}

Var ScatterSplitter::doActivityDecision() {
    vec<int> discarded;
    Var next = var_Undef;
    while (next == var_Undef || value(next) != l_Undef || !decision[next]) {
        if (order_heap.empty()) {
            if (discarded.size() > 0) {
                assert(splitContext.isInSplittingCycle());
                assert([&]() {
                    for (Var v : discarded) {
                        if (not isAssumptionVar(v)) {
                            throw PTPLib::common::Exception(__FILE__,__LINE__,";unable to split: all available variables have too long representations");
                        }
                    }
                    return true;
                }());

                // All available literals are assumption literals.  Instance is satisfiable
            } else {
                next = var_Undef;
            }
            break;
        } else {
            next = order_heap.removeMin();
            if (splitContext.isInSplittingCycle() && next != var_Undef) {
                if (isAssumptionVar(next)) {
                    discarded.push(next);
                    next = var_Undef;
                    // A hack!: Not branch on lengthy variables (more than 5000), basically not allowing split partition with too many nested lets
                } else if (this->theory_handler.getLogic().dumpWithLets(theory_handler.varToTerm(next)).length() > PTPLib::common::STATS.MAX_SIZE) {
                    discarded.push(next);
                    next = var_Undef;
                }
            }
        }
    }
    for (Var v : discarded)
        order_heap.insert(v);

    return next;
}

bool ScatterSplitter::scatterLevel() {
    int d;
    int currentSplitNum = static_cast<int>(splitContext.getCurrentSplitCount());
    int targetSplitNum = splitContext.splitTargetNumber();
    int splitsToDo = targetSplitNum - currentSplitNum;
    assert(splitsToDo > 0);
    // Current scattered instance number i = splits.size() + 1
    float r = 1/(float)(splitsToDo);
    for (int i = 1; ; i++) {
        // 2 << i == 2^(i+1)
        if ((2 << (i-1) <= splitsToDo) && (2 << i >= splitsToDo)) {
            // r-1(2^i) < 0 and we want absolute
            d = -(r-1/(float)(2<<(i-1))) > r-1/(float)(2<<i) ? i+1 : i;
            break;
        }
    }
    return d == decisionLevel() - assumptions.size();
}

opensmt::pair<SplitData,lbool> ScatterSplitter::createSplitAndBlockAssumptions() {
    SplitData splitData;
    vec<Lit> constraints_negated;
    vec<Lit> split_assumption;
    // Add the literals on the decision levels
    for (int i = assumptions.size(); i < decisionLevel(); i++) {
        Lit l = trail[trail_lim[i]];
        splitData.addConstraint<vec<Lit>>({l});
        // Remember this literal in the split assumptions vector of the
        // SAT solver
        split_assumption.push(l);
        // This will be added to the SAT formula to exclude the search
        // space
        constraints_negated.push(~l);
    }
    splitData.addSplitAssumptions(split_assumption);
    for (size_t i = 0; i < splitData.getSplitAssumptions().size()-1; i++) {
        vec<Lit> tmp;
        for (auto tr : splitData.getSplitAssumption(i)) {
            tmp.push(~tr);
        }
        splitData.addConstraint(tmp);
    }

    cancelUntil(0);
    lbool res = excludeAssumptions(constraints_negated) ? l_Undef : l_False;

    return {std::move(splitData), res};
}

bool ScatterSplitter::excludeAssumptions(vec<Lit> const & neg_constrs) {
    addOriginalClause(neg_constrs);
    simplify();
    return ok;
}


bool ScatterSplitter::okContinue() const {

    if (splitContext.solverLimit() and splitContext.solverLimit() == search_counter and not config.sat_split_mode()) {
        return false;
    } else if (getChannel().shouldStop()) {
        return false;
    } else if (conflicts % 1000 == 0 and splitContext.resourceLimitReached(search_counter)) {
        getChannel().setShouldStop();
        return false;
    } else if (static_cast<int>(splitContext.getCurrentSplitCount()) == splitContext.splitTargetNumber() - 1) {
        return false;
    }
    return true;
}
void ScatterSplitter::notifyEnd() {
    if (splitContext.solverLimit() and not config.sat_split_mode())
        return;
    if (isSplitTypeScatter()) {
        auto[data, result] = createSplitAndBlockAssumptions();
        splitContext.insertSplitData(std::move(data));
        if (result != l_False)
            throw PTPLib::common::Exception(__FILE__, __LINE__, ";assert: Instance not unsatisfiable after creating last partition.");
    }
    getChannel().setShouldStop();
}

lbool ScatterSplitter::solve_() {
    if (decisionLevel() != 0)
        throw PTPLib::common::Exception(__FILE__, __LINE__, ";assert: decision level is not zero at the start of the search!");
    if (isSplitTypeScatter()) {
        splitContext.reset(search_counter);
        splitContext.enterInitCycle(search_counter);
    }
    return CoreSMTSolver::solve_();
}

lbool ScatterSplitter::zeroLevelConflictHandler() {
    if (splitContext.hasSplits()) {
        getChannel().setShouldStop();
        return l_Undef;
    } else {
        return CoreSMTSolver::zeroLevelConflictHandler();
    }
}

CoreSMTSolver::ConsistencyAction ScatterSplitter::notifyConsistency() {
    if (splitContext.solverLimit() and not config.sat_split_mode())
        return ConsistencyAction::NoOp;

    if (not splitContext.isInSplittingCycle() and splitContext.shouldEnterSplittingCycle(search_counter)) {
        splitContext.enterSplittingCycle();
        return ConsistencyAction::BacktrackToZero;
    }
    if (splitContext.isInSplittingCycle() and scatterLevel()) {
        auto[data, result] = createSplitAndBlockAssumptions();
        splitContext.insertSplitData(std::move(data));
        if (result == l_False) { // Rest is unsat
            getChannel().setShouldStop();
            return ConsistencyAction::ReturnUndef;
        } else {
            splitContext.enterTuningCycle(search_counter);
            return ConsistencyAction::SkipToSearchBegin;
        }
    }
    return ConsistencyAction::NoOp;
}

bool ScatterSplitter::exposeClauses(std::vector<PTPLib::net::Lemma> & learnedLemmas) {
    int trail_max = this->trail_lim.size() == 0 ? this->trail.size() : this->trail_lim[0];
    trail_sent = std::max<int>(trail_sent, numTriviallyPropagatedOnDl0-1);
    assert(trail_sent >= 0);
    auto & logic = theory_handler.getLogic();
    for (int i = this->trail_sent; i < trail_max; i++) {
        this->trail_sent++;
        Lit l = trail[i];
        Var v = var(l);
        if (isAssumptionVar(v)) {
            continue;
        }
        auto pt = this->theory_handler.varToTerm(v);
        std::string str = logic.dumpWithLets(pt);
        assert([&](std::string_view clause_str) {
            if (clause_str.find(".frame") != std::string::npos) {
                throw PTPLib::common::Exception(__FILE__, __LINE__,"assert: frame caught in trail");
            }
            return true;
        }(str));
        pt = sign(l) ? logic.mkNot(pt) : pt;
        learnedLemmas.emplace_back(PTPLib::net::Lemma(logic.dumpWithLets(pt), 0));
    }

    for (CRef cr : learnts) {
        Clause &c = this->ca[cr];
        if (c.size() > static_cast<unsigned int>(3 + assumptions.size()) || c.mark() == 3)
            continue;
        int level = 0;
        vec<PTRef> clause;
        bool hasForeignAssumption = false;
        bool hasBulkyLit = false;
        std::size_t varSize = 0;
        for (Lit l : c) {
            Var v = var(l);
            varSize += this->theory_handler.getLogic().dumpWithLets(theory_handler.varToTerm(v)).length();
            if (varSize > PTPLib::common::STATS.MAX_SIZE) {
                hasBulkyLit = true;
                break;
            }
            if (isAssumptionVar(v)) {
                vec<opensmt::pair<int, int>> const & solverBranch_perVar = getBranchOfVar(v);
                if (isPrefix(solverBranch_perVar, getSolverBranch())) {
                    int result = solverBranch_perVar.size();
                    assert([&]() {
                        if (result <= 0) {
                            std::scoped_lock<std::mutex> s_lk(getChannel().getMutex());
                            throw PTPLib::common::Exception(__FILE__, __LINE__, ";assert: level is less than zero " +
                                getChannel().get_current_header().at(PTPLib::common::Param.NODE)+ std::to_string(result));
                        }
                        if (result > getSolverBranch().size()) {
                            std::scoped_lock<std::mutex> s_lk(getChannel().getMutex());
                            throw PTPLib::common::Exception(__FILE__, __LINE__, ";assert: level is greater than solver address length " +
                                getChannel().get_current_header().at(PTPLib::common::Param.NODE)+ std::to_string(result));
                        }
                        return true;
                    }());

                    level = std::max<int>(level, result);
                    continue;
                } else {
                    hasForeignAssumption = true;
                    break;
                }
// Second algorithm of how to correctly publish clauses so that they do not include assumption literals.
// https://github.com/usi-verification-and-security/opensmt/issues/499
//                auto getAssumptionLevel = [this](Var const & v) {
//                    assert(isAssumptionVar(v));
//                    int level = 0;
//                    for (Lit p : assumptions) {
//                        if (sign(p)) {
//                            ++level;
//                            if (var(p) == v)
//                                return level;
//                        }
//                    }
//                    return -1;
//                };
//                int result = getAssumptionLevel(v);
//                if (result >= 1) {
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
        if (hasBulkyLit or hasForeignAssumption or clause.size() > 3)
            continue;
        std::string str = logic.dumpWithLets(theory_handler.getLogic().mkOr(clause));
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

void ScatterSplitter::runPeriodic()
{
    if (firstPropagation) {
        assert(decisionLevel() == 0);
        firstPropagation = false;
        numTriviallyPropagatedOnDl0 = trail.size();
    }
    if (not getChannel().isClauseShareMode()) return;
    std::vector<PTPLib::net::Lemma> toPublishLemmas;
    if (getChannel().shouldLearnClauses()) {
        getChannel().clearShouldLearnClauses();

        if (exposeClauses(toPublishLemmas)) {
            {
                std::unique_lock<std::mutex> lk(getChannel().getMutex());
                if (not lk.owns_lock()) {
                    throw PTPLib::common::Exception(__FILE__, __LINE__,
                                                    ";assert: clause Learning couldn't take the lock");
                }
                getChannel().insert_learned_clause(std::move(toPublishLemmas));
            }
            if (syncedStream)
                syncedStream->println(getChannel().isColorMode() ? PTPLib::common::Color::FG_Green : PTPLib::common::Color::FG_DEFAULT,
                           "[t SEARCH ] -------------- add learned clauses to channel buffer, Size : ", toPublishLemmas.size());
        }
    }
}

void ScatterSplitter::mapEnabledFrameIdToVar(Var v, uint32_t fid, uint32_t & prevId) {
    if (prevId != UINT32_MAX and fid <= prevId) {
        throw PTPLib::common::Exception(__FILE__, __LINE__,";assert: en_frame order is not increasing");
    }
    prevId = fid;
    var_frameId[v] = fid ;
}

vec<opensmt::pair<int,int>> const & ScatterSplitter::getBranchOfVar(Var v) {
    return frameIdToSolverBranch[get_FrameId(v)];
}