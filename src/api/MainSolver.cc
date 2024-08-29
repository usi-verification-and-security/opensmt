/*
 *  Copyright (c) 2012 - 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2022 - 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "MainSolver.h"

#include <common/ApiException.h>
#include <itehandler/IteHandler.h>
#include <logics/ArrayTheory.h>
#include <logics/LATheory.h>
#include <logics/UFLATheory.h>
#include <models/ModelBuilder.h>
#include <rewriters/Substitutor.h>
#include <simplifiers/BoolRewriting.h>
#include <smtsolvers/GhostSMTSolver.h>
#include <smtsolvers/LookaheadSMTSolver.h>
#include <tsolvers/IDLTHandler.h>
#include <tsolvers/LATHandler.h>
#include <tsolvers/RDLTHandler.h>
#include <unsatcores/UnsatCoreBuilder.h>

namespace opensmt {

bool stop;

MainSolver::MainSolver(Logic & logic, SMTConfig & conf, std::string name)
    : theory(createTheory(logic, conf)),
      term_mapper(new TermMapper(logic)),
      thandler(new THandler(getTheory(), *term_mapper)),
      smt_solver(createInnerSolver(conf, *thandler)),
      logic(thandler->getLogic()),
      pmanager(logic),
      config(conf),
      ts(logic, *term_mapper),
      solver_name{std::move(name)} {
    conf.setUsedForInitiliazation();
    initialize();
}

MainSolver::MainSolver(std::unique_ptr<Theory> th, std::unique_ptr<TermMapper> tm, std::unique_ptr<THandler> thd,
                       std::unique_ptr<SimpSMTSolver> ss, Logic & logic, SMTConfig & conf, std::string name)
    : theory(std::move(th)),
      term_mapper(std::move(tm)),
      thandler(std::move(thd)),
      smt_solver(std::move(ss)),
      logic(thandler->getLogic()),
      pmanager(logic),
      config(conf),
      ts(logic, *term_mapper),
      solver_name{std::move(name)} {
    conf.setUsedForInitiliazation();
    initialize();
}

void MainSolver::initialize() {
    frames.push();
    frameTerms.push(logic.getTerm_true());
    preprocessor.initialize();
    smt_solver->initialize();
    pair<CRef, CRef> iorefs{CRef_Undef, CRef_Undef};
    smt_solver->addOriginalSMTClause({term_mapper->getOrCreateLit(logic.getTerm_true())}, iorefs);
    if (iorefs.first != CRef_Undef) { pmanager.addClauseClassMask(iorefs.first, 1); }

    smt_solver->addOriginalSMTClause({~term_mapper->getOrCreateLit(logic.getTerm_false())}, iorefs);
    if (iorefs.first != CRef_Undef) { pmanager.addClauseClassMask(iorefs.first, 1); }
}

void MainSolver::push() {
    bool alreadyUnsat = isLastFrameUnsat();
    frames.push();
    preprocessor.push();
    frameTerms.push(newFrameTerm(frames.last().getId()));
    if (alreadyUnsat) { rememberLastFrameUnsat(); }
}

bool MainSolver::pop() {
    if (frames.frameCount() > 1) {
        if (trackPartitions()) {
            auto const & partitionsToInvalidate = frames.last().formulas;
            ipartitions_t mask = 0;
            for (PTRef partition : partitionsToInvalidate) {
                auto index = pmanager.getPartitionIndex(partition);
                assert(index != -1);
                setbit(mask, static_cast<unsigned int>(index));
            }
            pmanager.invalidatePartitions(mask);
        }
        frames.pop();
        preprocessor.pop();
        firstNotSimplifiedFrame = std::min(firstNotSimplifiedFrame, frames.frameCount());
        if (not isLastFrameUnsat()) { getSMTSolver().restoreOK(); }
        return true;
    }
    return false;
}

void MainSolver::insertFormula(PTRef fla) {
    if (logic.getSortRef(fla) != logic.getSort_bool()) {
        throw ApiException("Top-level assertion sort must be Bool, got " + logic.printSort(logic.getSortRef(fla)));
    }
    // TODO: Move this to preprocessing of the formulas
    fla = IteHandler(logic, getPartitionManager().getNofPartitions()).rewrite(fla);

    if (trackPartitions()) {
        // MB: Important for HiFrog! partition index is the index of the formula in an virtual array of inserted
        // formulas,
        //     thus we need the old value of count. TODO: Find a good interface for this so it cannot be broken this
        //     easily
        unsigned int partition_index = insertedFormulasCount++;
        pmanager.assignTopLevelPartitionIndex(partition_index, fla);
        assert(pmanager.getPartitionIndex(fla) != -1);
    } else {
        ++insertedFormulasCount;
    }

    frames.add(fla);
    firstNotSimplifiedFrame = std::min(firstNotSimplifiedFrame, frames.frameCount() - 1);
}

sstat MainSolver::simplifyFormulas() {
    status = s_Undef;
    for (std::size_t i = firstNotSimplifiedFrame; i < frames.frameCount() && status != s_False; i++) {
        PreprocessingContext context{.frameCount = i, .perPartition = trackPartitions()};
        preprocessor.prepareForProcessingFrame(i);
        firstNotSimplifiedFrame = i + 1;
        if (context.perPartition) {
            vec<PTRef> frameFormulas;
            for (PTRef fla : frames[i].formulas) {
                PTRef processed = theory->preprocessAfterSubstitutions(fla, context);
                pmanager.transferPartitionMembership(fla, processed);
                frameFormulas.push(processed);
                preprocessor.addPreprocessedFormula(processed);
            }
            if (frameFormulas.size() == 0 or std::all_of(frameFormulas.begin(), frameFormulas.end(),
                                                         [&](PTRef fla) { return fla == logic.getTerm_true(); })) {
                continue;
            }
            theory->afterPreprocessing(preprocessor.getPreprocessedFormulas());
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
            PTRef frameFormula = logic.mkAnd(frames[i].formulas);
            if (context.frameCount > 0) { frameFormula = applyLearntSubstitutions(frameFormula); }
            frameFormula = theory->preprocessBeforeSubstitutions(frameFormula, context);
            frameFormula = substitutionPass(frameFormula, context);
            frameFormula = theory->preprocessAfterSubstitutions(frameFormula, context);

            if (logic.isFalse(frameFormula)) {
                giveToSolver(logic.getTerm_false(), frames[i].getId());
                status = s_False;
                break;
            }
            preprocessor.addPreprocessedFormula(frameFormula);
            theory->afterPreprocessing(preprocessor.getPreprocessedFormulas());
            // Optimize the dag for cnfization
            if (logic.isBooleanOperator(frameFormula)) { frameFormula = rewriteMaxArity(frameFormula); }
            status = giveToSolver(frameFormula, frames[i].getId());
        }
    }
    if (status == s_False) {
        assert(firstNotSimplifiedFrame > 0);
        rememberUnsatFrame(firstNotSimplifiedFrame - 1);
    }
    return status;
}

void MainSolver::printFramesAsQuery(std::ostream & s) const {
    logic.dumpHeaderToFile(s);
    for (std::size_t i = 0; i < frames.frameCount(); ++i) {
        if (i > 0) s << "(push 1)\n";
        for (PTRef assertion : frames[i].formulas) {
            logic.dumpFormulaToFile(s, assertion);
        }
    }
    logic.dumpChecksatToFile(s);
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
PTRef MainSolver::rewriteMaxArity(PTRef root) {
    return opensmt::rewriteMaxArityClassic(logic, root);
}

std::unique_ptr<Model> MainSolver::getModel() {
    if (!config.produce_models()) { throw ApiException("Producing models is not enabled"); }
    if (status != s_True) { throw ApiException("Model cannot be created if solver is not in SAT state"); }

    ModelBuilder modelBuilder{logic};
    smt_solver->fillBooleanVars(modelBuilder);
    thandler->fillTheoryFunctions(modelBuilder);

    return modelBuilder.build();
}

void MainSolver::printResolutionProofSMT2() const {
    assert(smt_solver);
    if (!smt_solver->logsResolutionProof()) { throw ApiException("Proofs are not tracked"); }
    if (status != s_False) { throw ApiException("Proof cannot be created if solver is not in UNSAT state"); }

    return smt_solver->printResolutionProofSMT2(std::cout);
}

std::unique_ptr<UnsatCore> MainSolver::getUnsatCore() const {
    if (not config.produce_unsat_cores()) { throw ApiException("Producing unsat cores is not enabled"); }
    if (status != s_False) { throw ApiException("Unsat core cannot be extracted if solver is not in UNSAT state"); }

    UnsatCoreBuilder unsatCoreBuilder{&config, &smt_solver->getResolutionProof(), &pmanager};

    return unsatCoreBuilder.build();
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
    if (!config.produce_inter()) { throw ApiException("Producing interpolants is not enabled"); }
    if (status != s_False) {
        throw ApiException("Interpolation context cannot be created if solver is not in UNSAT state");
    }
    return std::make_unique<InterpolationContext>(config, *theory, *term_mapper, getSMTSolver().getResolutionProof(),
                                                  pmanager);
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

void MainSolver::printFramesAsQuery() const {
    char * base_name = config.dump_query_name();
    if (base_name == NULL)
        printFramesAsQuery(std::cout);
    else {
        char * s_file_name;
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

sstat MainSolver::giveToSolver(PTRef root, FrameId push_id) {

    struct ClauseCallBack : public Cnfizer::ClauseCallBack {
        std::vector<vec<Lit>> clauses;
        void operator()(vec<Lit> && c) override { clauses.push_back(std::move(c)); }
    };
    ClauseCallBack callBack;
    ts.setClauseCallBack(&callBack);
    ts.Cnfizer::cnfize(root, push_id);
    bool const keepPartitionsSeparate = trackPartitions();
    Lit frameLit = push_id == 0 ? Lit{} : term_mapper->getOrCreateLit(frameTerms[push_id]);
    int partitionIndex = keepPartitionsSeparate ? pmanager.getPartitionIndex(root) : -1;
    for (auto & clause : callBack.clauses) {
        if (push_id != 0) { clause.push(frameLit); }
        pair<CRef, CRef> iorefs{CRef_Undef, CRef_Undef};
        bool res = smt_solver->addOriginalSMTClause(std::move(clause), iorefs);
        if (keepPartitionsSeparate) {
            CRef ref = iorefs.first;
            if (ref != CRef_Undef) {
                ipartitions_t parts = 0;
                assert(partitionIndex != -1);
                setbit(parts, static_cast<unsigned int>(partitionIndex));
                pmanager.addClauseClassMask(ref, parts);
            }
        }
        if (not res) { return s_False; }
    }
    return s_Undef;
}

sstat MainSolver::check() {
    ++check_called;
    if (config.timeQueries()) {
        printf("; %s query time so far: %f\n", solver_name.c_str(), query_timer.getTime());
        StopWatch sw(query_timer);
    }
    if (isLastFrameUnsat()) { return s_False; }
    sstat rval = simplifyFormulas();

    if (config.dump_query()) printFramesAsQuery();

    if (rval == s_Undef) {
        try {
            rval = solve();
        } catch (std::overflow_error const & error) { rval = s_Error; }
        if (rval == s_False) {
            assert(not smt_solver->isOK());
            rememberUnsatFrame(smt_solver->getConflictFrame());
        }
    }

    return rval;
}

sstat MainSolver::solve() {
    if (!smt_solver->isOK()) { return s_False; }

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

    if (status == s_True && config.produce_models()) thandler->computeModel();
    smt_solver->clearSearch();
    return status;
}

sstat MainSolver::solve_(vec<FrameId> const & enabledFrames) {
    assert(frameTerms.size() > 0 and frameTerms[0] == getLogic().getTerm_true());
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
        assumps[fid] = ~assumps[fid];
        smt_solver->mapEnabledFrameIdToVar(var(assumps[fid]), fid, prevId);
    }
    // Drop the assumption variable for the base frame (it is at the first place)
    for (int i = 1; i < assumps.size(); ++i) {
        assumps[i - 1] = assumps[i];
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
    Logic_t logicType = logic.getLogic();
    Theory * theory = nullptr;
    switch (logicType) {
        case Logic_t::QF_UF:
        case Logic_t::QF_BOOL: {
            theory = new UFTheory(config, logic);
            break;
        }
        case Logic_t::QF_AX: {
            theory = new ArrayTheory(config, logic);
            break;
        }
        case Logic_t::QF_LRA: {
            ArithLogic & lraLogic = dynamic_cast<ArithLogic &>(logic);
            theory = new LATheory<ArithLogic, LATHandler>(config, lraLogic);
            break;
        }
        case Logic_t::QF_LIA: {
            ArithLogic & liaLogic = dynamic_cast<ArithLogic &>(logic);
            theory = new LATheory<ArithLogic, LATHandler>(config, liaLogic);
            break;
        }
        case Logic_t::QF_RDL: {
            ArithLogic & lraLogic = dynamic_cast<ArithLogic &>(logic);
            theory = new LATheory<ArithLogic, RDLTHandler>(config, lraLogic);
            break;
        }
        case Logic_t::QF_IDL: {
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
        case Logic_t::QF_AUFLIRA: {
            ArithLogic & laLogic = dynamic_cast<ArithLogic &>(logic);
            theory = new UFLATheory(config, laLogic);
            break;
        }
        case Logic_t::UNDEF:
            throw ApiException{"Error in creating reasoning engine: Engine type not specified"};
            break;
        default:
            assert(false);
            throw std::logic_error{"Unreachable code - error in logic selection"};
    };

    return std::unique_ptr<Theory>(theory);
}

PTRef MainSolver::applyLearntSubstitutions(PTRef fla) {
    Logic::SubstMap knownSubst = preprocessor.getCurrentSubstitutions();
    PTRef res = Substitutor(getLogic(), knownSubst).rewrite(fla);
    return res;
}

PTRef MainSolver::substitutionPass(PTRef fla, PreprocessingContext const & context) {
    if (not config.do_substitutions()) { return fla; }
    auto res = computeSubstitutions(fla);
    vec<PTRef> args;
    auto const & entries = res.usedSubstitution.getKeys();
    for (auto entry : entries) {
        auto target = res.usedSubstitution[entry];
        args.push(logic.mkEq(entry, target));
    }
    args.push(res.result);
    PTRef withSubs = logic.mkAnd(std::move(args));

    preprocessor.setSubstitutions(context.frameCount, std::move(res.usedSubstitution));
    return withSubs;
}

MainSolver::SubstitutionResult MainSolver::computeSubstitutions(PTRef fla) {
    SubstitutionResult result;
    assert(getConfig().do_substitutions() and not getSMTSolver().logsResolutionProof());
    PTRef root = fla;
    Logic::SubstMap allsubsts;
    while (true) {
        // update the current simplification formula
        PTRef simp_formula = root;
        // l_True : exists and is valid
        // l_False : exists but has been disabled to break symmetries
        MapWithKeys<PTRef, lbool, PTRefHash> new_units;
        vec<PtAsgn> current_units_vec;
        bool rval = logic.getNewFacts(simp_formula, new_units);
        if (not rval) { return SubstitutionResult{{}, logic.getTerm_false()}; }
        // Add the newly obtained units to the list of all substitutions
        // Clear the previous units
        auto const & new_units_vec = new_units.getKeys();
        for (PTRef key : new_units_vec) {
            current_units_vec.push(PtAsgn{key, new_units[key]});
        }

        auto [res, newsubsts] = logic.retrieveSubstitutions(current_units_vec);
        logic.substitutionsTransitiveClosure(newsubsts);

        // remember the substitutions for models
        for (PTRef key : newsubsts.getKeys()) {
            if (!allsubsts.has(key)) {
                auto const target = newsubsts[key];
                allsubsts.insert(key, target);
            }
        }

        if (res != l_Undef) root = (res == l_True ? logic.getTerm_true() : logic.getTerm_false());

        PTRef new_root = Substitutor(logic, newsubsts).rewrite(root);

        bool cont = new_root != root;
        root = new_root;
        if (!cont) break;
    }
    result.result = root;
    result.usedSubstitution = std::move(allsubsts);
    return result;
}

void MainSolver::Preprocessor::initialize() {
    substitutions.push();
}

void MainSolver::Preprocessor::prepareForProcessingFrame(std::size_t frameIndex) {
    assert(frameIndex < solverFrameCount);
    while (internalFrameCount <= frameIndex) {
        pushInternal();
    }
}
void MainSolver::Preprocessor::push() {
    assert(solverFrameCount >= internalFrameCount);
    ++solverFrameCount;
}

void MainSolver::Preprocessor::pop() {
    assert(solverFrameCount >= internalFrameCount);
    --solverFrameCount;
    if (solverFrameCount >= internalFrameCount) { return; }
    popInternal();
    assert(solverFrameCount == internalFrameCount);
}

void MainSolver::Preprocessor::pushInternal() {
    ++internalFrameCount;
    substitutions.push();
    preprocessedFormulas.pushScope();
}

void MainSolver::Preprocessor::popInternal() {
    --internalFrameCount;
    substitutions.pop();
    preprocessedFormulas.popScope();
}

void MainSolver::Preprocessor::addPreprocessedFormula(PTRef fla) {
    preprocessedFormulas.push(fla);
}

span<PTRef const> MainSolver::Preprocessor::getPreprocessedFormulas() const {
    return {preprocessedFormulas.data(), static_cast<uint32_t>(preprocessedFormulas.size())};
}
} // namespace opensmt
