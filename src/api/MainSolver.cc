/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/


#include "MainSolver.h"
#include "BoolRewriting.h"
#include "LookaheadSMTSolver.h"
#include "GhostSMTSolver.h"
#include "UFLATheory.h"
#include "LATheory.h"
#include "LATHandler.h"
#include "ArrayTheory.h"
#include "OsmtApiException.h"
#include "ModelBuilder.h"
#include "IteHandler.h"
#include "RDLTHandler.h"
#include "IDLTHandler.h"
#include <thread>
#include <fcntl.h>

namespace opensmt { bool stop; }

void MainSolver::initialize() {
    smt_solver->initialize();
    opensmt::pair<CRef, CRef> iorefs{CRef_Undef, CRef_Undef};
    smt_solver->addOriginalSMTClause({term_mapper->getOrCreateLit(logic.getTerm_true())}, iorefs);
    if (iorefs.first != CRef_Undef) { pmanager.addClauseClassMask(iorefs.first, 1); }

    smt_solver->addOriginalSMTClause({~term_mapper->getOrCreateLit(logic.getTerm_false())}, iorefs);
    if (iorefs.first != CRef_Undef) { pmanager.addClauseClassMask(iorefs.first, 1); }
}

void
MainSolver::push()
{
    bool alreadyUnsat = isLastFrameUnsat();
    frames.push();
    frameTerms.push(newFrameTerm(frames.last().getId()));
    if (alreadyUnsat) { rememberLastFrameUnsat(); }
}

bool
MainSolver::pop()
{
    if (frames.frameCount() > 1) {
        if (config.produce_inter() > 0) {
            auto const & partitionsToInvalidate = frames.last().formulas;
            ipartitions_t mask = 0;
            for (PTRef partition : partitionsToInvalidate) {
                auto index = pmanager.getPartitionIndex(partition);
                assert(index != -1);
                opensmt::setbit(mask, static_cast<unsigned int>(index));
            }
            pmanager.invalidatePartitions(mask);
        }
        frames.pop();
        firstNotSimplifiedFrame = std::min(firstNotSimplifiedFrame, frames.frameCount());
        if (not isLastFrameUnsat()) {
            getSMTSolver().restoreOK();
        }
        return true;
    }
    return false;
}

PTRef MainSolver::newFrameTerm(MainSolver::FrameId frameId) {
    assert(frameId.id != 0);
    auto name = std::string(Logic::s_framev_prefix) + std::to_string(frameId.id);
    PTRef frameTerm = logic.mkBoolVar(name.c_str());
    Lit l = term_mapper->getOrCreateLit(frameTerm);
    term_mapper->setFrozen(var(l));
    smt_solver->addAssumptionVar(var(l));
    return frameTerm;
}

void MainSolver::insertFormula(PTRef fla)
{
    if (logic.getSortRef(fla) != logic.getSort_bool()) {
        throw OsmtApiException("Top-level assertion sort must be Bool, got " + logic.printSort(logic.getSortRef(fla)));
    }

    // TODO: Move this to preprocessing of the formulas
    fla = IteHandler(logic, getPartitionManager().getNofPartitions()).rewrite(fla);

    if (getConfig().produce_inter()) {
        // MB: Important for HiFrog! partition index is the index of the formula in an virtual array of inserted formulas,
        //     thus we need the old value of count. TODO: Find a good interface for this so it cannot be broken this easily
        unsigned int partition_index = inserted_formulas_count++;
        pmanager.assignTopLevelPartitionIndex(partition_index, fla);
        assert(pmanager.getPartitionIndex(fla) != -1);
    }
    else {
        ++inserted_formulas_count;
    }

    frames.add(fla);
    firstNotSimplifiedFrame = std::min(firstNotSimplifiedFrame, frames.frameCount() - 1);
}

sstat MainSolver::simplifyFormulas()
{
    status = s_Undef;
    bool keepPartitionsSeparate = getConfig().produce_inter();
    // Process (and simplify) not yet processed frames. Stop processing if solver is in UNSAT state already
    for (std::size_t i = firstNotSimplifiedFrame; i < frames.frameCount() && status != s_False; i++) {
        if (keepPartitionsSeparate) {
            vec<PTRef> frameFormulas = getTheory().simplifyIndividually(frames[i].formulas, pmanager, i == 0);
            firstNotSimplifiedFrame = i + 1;
            if (frameFormulas.size() == 0 or std::all_of(frameFormulas.begin(), frameFormulas.end(), [&](PTRef fla) { return fla == logic.getTerm_true(); })) {
                continue;
            }
            for (PTRef fla : frameFormulas) {
                if (fla == logic.getTerm_true()) { continue; }
                assert(pmanager.getPartitionIndex(fla) != -1);
                // Optimize the dag for cnfization
                if (logic.isBooleanOperator(fla)) {
                    PTRef old = fla;
                    fla = rewriteMaxArity(fla);
                    pmanager.transferPartitionMembership(old, fla);
                }
                assert(pmanager.getPartitionIndex(fla) != -1);
                pmanager.propagatePartitionMask(fla);
                status = giveToSolver(fla, frames[i].getId());
                if (status == s_False) { break; }
            }
        } else {
            PTRef frameFormula = getTheory().simplifyTogether(frames[i].formulas, i == 0);
            firstNotSimplifiedFrame = i + 1;
            if (logic.isFalse(frameFormula)) {
                giveToSolver(getLogic().getTerm_false(), frames[i].getId());
                status = s_False;
                break;
            }
            // Optimize the dag for cnfization
            if (logic.isBooleanOperator(frameFormula)) {
                frameFormula = rewriteMaxArity(frameFormula);
            }
            status = giveToSolver(frameFormula, frames[i].getId());
        }
    }
    if (status == s_False) {
        assert(firstNotSimplifiedFrame > 0);
        rememberUnsatFrame(firstNotSimplifiedFrame - 1);
    }
    return status;
}


// Replace subtrees consisting only of ands / ors with a single and / or term.
// Search a maximal section of the tree consisting solely of ands / ors.  The
// root of this subtree is called and / or root.  Collect the subtrees rooted at
// the leaves of this section, and create a new and / or term with the leaves as
// arguments and the parent of the and / or tree as the parent.
//
// However, we will do this in a clever way so that if a certain
// term appears as a child in more than one term, we will not flatten
// that structure.
//
PTRef MainSolver::rewriteMaxArity(PTRef root)
{
    return ::rewriteMaxArityClassic(logic, root);
}

std::unique_ptr<Model> MainSolver::getModel() {
    if (status != s_True) { throw OsmtApiException("Model cannot be created if solver is not in SAT state"); }

    ModelBuilder modelBuilder {logic};
    smt_solver->fillBooleanVars(modelBuilder);
    thandler->fillTheoryFunctions(modelBuilder);

    return modelBuilder.build();
}

lbool MainSolver::getTermValue(PTRef tr) const {
    if (logic.getSortRef(tr) != logic.getSort_bool()) { return l_Undef; }
    if (not term_mapper->hasLit(tr)) { return l_Undef; }

    Lit l = term_mapper->getLit(tr);
    auto val = smt_solver->modelValue(l);
    assert(val != l_Undef);
    return val;
}

std::unique_ptr<InterpolationContext> MainSolver::getInterpolationContext() {
    if (status != s_False) { throw OsmtApiException("Interpolation context cannot be created if solver is not in UNSAT state"); }
    return std::make_unique<InterpolationContext>(
            config, *theory, *term_mapper, getSMTSolver().getProof(), pmanager
    );
}

PTRef MainSolver::currentRootInstance() const {
    vec<PTRef> assertions;
    for (auto i = 0u; i < frames.frameCount(); i++) {
        auto const & frameAssertions = frames[i].formulas;
        for (PTRef assertion : frameAssertions) {
            assertions.push(assertion);
        }
    }
    return logic.mkAnd(std::move(assertions));
}

void MainSolver::printFramesAsQuery() const
{
    char* base_name = config.dump_query_name();
    if (base_name == NULL)
        printFramesAsQuery(std::cout);
    else {
        char* s_file_name;
        int chars_written = asprintf(&s_file_name, "%s-%d.smt2", base_name, check_called);
        (void)chars_written;
        std::ofstream stream;
        stream.open(s_file_name);
        printFramesAsQuery(stream);
        stream.close();
        free(s_file_name);
    }
    free(base_name);
}

sstat MainSolver::giveToSolver(PTRef root, MainSolver::FrameId push_id) {

    struct ClauseCallBack : public Cnfizer::ClauseCallBack {
        std::vector<vec<Lit>> clauses;
        void operator()(vec<Lit> && c) override {
            clauses.push_back(std::move(c));
        }
    };
    ClauseCallBack callBack;
    ts.setClauseCallBack(&callBack);
    ts.Cnfizer::cnfize(root, push_id.id);
    bool keepPartitionsSeparate = getConfig().produce_inter();
    Lit frameLit = push_id.id == 0 ? Lit{} : term_mapper->getOrCreateLit(frameTerms[push_id.id]);
    int partitionIndex = keepPartitionsSeparate ? pmanager.getPartitionIndex(root) : -1;
    for (auto & clause : callBack.clauses) {
        if (push_id.id != 0) {
            clause.push(frameLit);
        }
        opensmt::pair<CRef, CRef> iorefs{CRef_Undef, CRef_Undef};
        bool res = smt_solver->addOriginalSMTClause(std::move(clause), iorefs);
        if (keepPartitionsSeparate) {
            CRef ref = iorefs.first;
            if (ref != CRef_Undef) {
                ipartitions_t parts = 0;
                assert(partitionIndex != -1);
                opensmt::setbit(parts, static_cast<unsigned int>(partitionIndex));
                pmanager.addClauseClassMask(ref, parts);
            }
        }
        if (not res) { return s_False; }
    }
    return s_Undef;
}

sstat MainSolver::check()
{
    ++check_called;
    if (config.timeQueries()) {
        printf("; %s query time so far: %f\n", solver_name.c_str(), query_timer.getTime());
        opensmt::StopWatch sw(query_timer);
    }
    if (isLastFrameUnsat()) {
        return s_False;
    }
    sstat rval = simplifyFormulas();

    if (config.dump_query())
        printFramesAsQuery();

    if (rval == s_Undef) {
        try {
            rval = solve();
        } catch (std::overflow_error const& error) {
            rval = s_Error;
        }
        if (rval == s_False) {
            assert(not smt_solver->isOK());
            rememberUnsatFrame(smt_solver->getConflictFrame());
        }
    }

    return rval;
}

sstat MainSolver::solve()
{
    if (!smt_solver->isOK()){
        return s_False;
    }

    // FIXME: Find a better way to deal with Bools in UF
    for (PTRef tr : logic.propFormulasAppearingInUF) {
        Lit l = term_mapper->getOrCreateLit(tr);
        smt_solver->addVar(var(l));
    }

    vec<FrameId> en_frames;
    for (std::size_t i = 0; i < frames.frameCount(); ++i) {
        en_frames.push(frames[i].getId());
    }
    status = solve_(en_frames);

    if (status == s_True && config.produce_models())
        thandler->computeModel();
    smt_solver->clearSearch();
    return status;
}

sstat MainSolver::solve_(vec<FrameId> const & enabledFrames) {
    assert(frameTerms.size() > 0 and frameTerms[0] == logic.getTerm_true());
    vec<Lit> assumps;
    // Initialize so that by default frames are disabled
    for (PTRef tr : frameTerms) {
        assumps.push(term_mapper->getOrCreateLit(tr));
    }

    // Enable the terms which are listed in enabledFrames
    // At this point assumps has the same size as frame_terms and the
    // elements are in the same order.  We simply invert the
    // corresponding literals
    uint32_t prevId = UINT32_MAX;
    for (FrameId fid : enabledFrames) {
        assumps[fid.id] = ~assumps[fid.id];
        smt_solver->mapEnabledFrameIdToVar(var(assumps[fid.id]), fid.id, prevId);
    }
    // Drop the assumption variable for the base frame (it is at the first place)
    for (int i = 1; i < assumps.size(); ++i) {
        assumps[i-1] = assumps[i];
    }
    assumps.pop();
    return smt_solver->solve(assumps, !config.isIncremental(), config.isIncremental());
}

std::unique_ptr<SimpSMTSolver> MainSolver::createInnerSolver(SMTConfig & config, THandler & thandler) {
    if (config.sat_pure_lookahead()) {
        return std::make_unique<LookaheadSMTSolver>(config, thandler);
    } else if (config.use_ghost_vars()) {
        return std::make_unique<GhostSMTSolver>(config, thandler);
    } else if (config.sat_picky()) {
    return std::make_unique<LookaheadSMTSolver>(config, thandler);
    } else {
        return std::make_unique<SimpSMTSolver>(config, thandler);
    }
}

std::unique_ptr<Theory> MainSolver::createTheory(Logic & logic, SMTConfig & config) {
    using Logic_t = opensmt::Logic_t;
    Logic_t logicType = logic.getLogic();
    Theory* theory = nullptr;
    switch (logicType) {
        case Logic_t::QF_UF:
        case Logic_t::QF_BOOL:
        {
            theory = new UFTheory(config, logic);
            break;
        }
        case Logic_t::QF_AX:
        {
            theory = new ArrayTheory(config, logic);
            break;
        }
        case Logic_t::QF_LRA:
        {
            ArithLogic & lraLogic = dynamic_cast<ArithLogic &>(logic);
            theory = new LATheory<ArithLogic,LATHandler>(config, lraLogic);
            break;
        }
        case Logic_t::QF_LIA:
        {
            ArithLogic & liaLogic = dynamic_cast<ArithLogic &>(logic);
            theory = new LATheory<ArithLogic,LATHandler>(config, liaLogic);
            break;
        }
        case Logic_t::QF_RDL:
        {
            ArithLogic& lraLogic = dynamic_cast<ArithLogic &>(logic);
            theory = new LATheory<ArithLogic, RDLTHandler>(config, lraLogic);
            break;
        }
        case Logic_t::QF_IDL:
        {
            ArithLogic & liaLogic = dynamic_cast<ArithLogic &>(logic);
            theory = new LATheory<ArithLogic, IDLTHandler>(config, liaLogic);
            break;
        }
        case Logic_t::QF_UFRDL:
        case Logic_t::QF_UFIDL:
        case Logic_t::QF_UFLRA:
        case Logic_t::QF_UFLIA:
        case Logic_t::QF_ALRA:
        case Logic_t::QF_ALIA:
        case Logic_t::QF_AUFLRA:
        case Logic_t::QF_AUFLIA:
        case Logic_t::QF_AUFLIRA:
        {
            ArithLogic & laLogic = dynamic_cast<ArithLogic &>(logic);
            theory = new UFLATheory(config, laLogic);
            break;
        }
        case Logic_t::UNDEF:
            throw OsmtApiException{"Error in creating reasoning engine: Engige type not specified"};
            break;
        default:
            assert(false);
            throw std::logic_error{"Unreachable code - error in logic selection"};

    };

    return std::unique_ptr<Theory>(theory);
}
