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

#include <type_traits>

namespace opensmt {

MainSolver::MainSolver(Logic & logic, SMTConfig & conf, std::string name)
    : theory(createTheory(logic, conf)),
      term_mapper(new TermMapper(logic)),
      thandler(new THandler(getTheory(), *term_mapper)),
      smt_solver(createInnerSolver(conf, *thandler)),
      termNames(conf),
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
      termNames(conf),
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
    preprocessedAssertionsCountPerFrame.push_back(0);
    preprocessedAssertionsPerFrame.push_back(PTRef_Undef);
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
    preprocessedAssertionsCountPerFrame.push_back(0);
    preprocessedAssertionsPerFrame.push_back(PTRef_Undef);
    termNames.pushScope();
    if (alreadyUnsat) { rememberLastFrameUnsat(); }
}

bool MainSolver::pop() {
    if (getAssertionLevel() == 0) { return false; }

    if (trackPartitions()) {
        ipartitions_t mask = 0;
        for (PTRef partition : getAssertionsAtCurrentLevel()) {
            auto index = pmanager.getPartitionIndex(partition);
            assert(index != -1);
            setbit(mask, static_cast<unsigned int>(index));
        }
        pmanager.invalidatePartitions(mask);
    }
    frames.pop();
    preprocessor.pop();
    preprocessedAssertionsCountPerFrame.pop_back();
    preprocessedAssertionsPerFrame.pop_back();
    termNames.popScope();
    // goes back to frames.frameCount()-1 only if a formula is added via addAssertion
    firstNotPreprocessedFrame = std::min(firstNotPreprocessedFrame, frames.frameCount());
    if (not isLastFrameUnsat()) { getSMTSolver().restoreOK(); }
    return true;
}

std::size_t MainSolver::getAssertionLevel() const {
    assert(frames.frameCount() >= 1);
    return frames.frameCount() - 1;
}

void MainSolver::insertFormula(PTRef fla) {
    if (logic.getSortRef(fla) != logic.getSort_bool()) {
        throw ApiException("Top-level assertion sort must be Bool, got " + logic.sortToString(logic.getSortRef(fla)));
    }

    if (trackPartitions()) {
        // MB: Important for HiFrog! partition index is the index of the formula in an virtual array of inserted
        // formulas,
        //     thus we need the old value of count. TODO: Find a good interface for this so it cannot be broken this
        //     easily
        unsigned int partition_index = insertedAssertionsCount++;
        pmanager.assignTopLevelPartitionIndex(partition_index, fla);
        assert(pmanager.getPartitionIndex(fla) != -1);
    } else {
        ++insertedAssertionsCount;
    }

    frames.add(fla);
    firstNotPreprocessedFrame = std::min(firstNotPreprocessedFrame, frames.frameCount() - 1);
}

bool MainSolver::tryAddNamedAssertion(PTRef fla, std::string const & name) {
    bool const success = tryAddTermNameFor(fla, name);
    if (not success) { return false; }

    addAssertion(fla);
    return true;
}

bool MainSolver::tryAddTermNameFor(PTRef fla, std::string const & name) {
    return termNames.tryInsert(name, fla);
}

sstat MainSolver::simplifyFormulas() {
    status = s_Undef;
    for (std::size_t i = firstNotPreprocessedFrame; i < frames.frameCount(); ++i) {
        assert(status != s_False);
        if (tryPreprocessFormulasOfFrame(i)) { continue; }
        assert(status == s_False);
        break;
    }

    if (status == s_False) {
        assert(firstNotPreprocessedFrame > 0);
        rememberUnsatFrame(firstNotPreprocessedFrame - 1);
    }

    return status;
}

bool MainSolver::tryPreprocessFormulasOfFrame(std::size_t i) {
    auto & frame = frames[i];
    FrameId const frameId = frame.getId();
    auto & preprocessedFrameAssertionsCount = preprocessedAssertionsCountPerFrame[i];
    auto & preprocessedFrameAssertions = preprocessedAssertionsPerFrame[i];
    assert(frame.formulas.size() == 0 or std::size_t(frame.formulas.size()) > preprocessedFrameAssertionsCount);
    PreprocessingContext context{.frameCount = i,
                                 .preprocessedFrameAssertionsCount = preprocessedFrameAssertionsCount,
                                 .preprocessedFrameAssertions = preprocessedFrameAssertions,
                                 .perPartition = trackPartitions()};
    preprocessor.prepareForProcessingFrame(i);
    firstNotPreprocessedFrame = i + 1;
    preprocessedFrameAssertionsCount = frame.formulas.size();

    assert(status != s_False);

    if (not context.perPartition) {
        PTRef frameFormula = preprocessFormulasDefault(frame.formulas, context);
        status = giveToSolver(frameFormula, frameId);
        if (status == s_False) { return false; }
        preprocessedFrameAssertions = frameFormula;
        return true;
    }

    vec<PTRef> processedFormulas = preprocessFormulasPerPartition(frame.formulas, context);
    // no need to update preprocessedFrameAssertions, not used here
    for (PTRef fla : processedFormulas) {
        status = giveToSolver(fla, frameId);
        if (status == s_False) { return false; }
    }

    assert(status != s_False);
    return true;
}

PTRef MainSolver::preprocessFormulasDefault(vec<PTRef> const & frameFormulas, PreprocessingContext const & context) {
    assert(not context.perPartition);

    std::size_t const frameFormulasCount = frameFormulas.size();
    static_assert(std::is_unsigned_v<decltype(context.preprocessedFrameAssertionsCount)>);
    assert(context.preprocessedFrameAssertionsCount <= frameFormulasCount);
    std::size_t const formulasCountToProcess = frameFormulasCount - context.preprocessedFrameAssertionsCount;
    if (formulasCountToProcess == 0) { return logic.getTerm_true(); }

    bool const processAll = formulasCountToProcess == frameFormulasCount;

    PTRef frameFormula = [&] {
        if (processAll) { return logic.mkAnd(frameFormulas); }

        vec<PTRef> processedFormulas;
        for (std::size_t i = context.preprocessedFrameAssertionsCount; i < frameFormulasCount; ++i) {
            processedFormulas.push(frameFormulas[i]);
        }
        return logic.mkAnd(std::move(processedFormulas));
    }();

    // All frame formulas are always somehow preprocessed
    preprocessedAssertionsCount += frameFormulas.size();

    if (processAll) {
        assert(context.preprocessedFrameAssertions == PTRef_Undef or
               context.preprocessedFrameAssertions == logic.getTerm_true());
        return preprocessFormula(frameFormula, context);
    }

    // Still put together with already preprocessed formulas which can still benefit from the new ones
    frameFormula = preprocessFormulaItes(frameFormula, context);
    assert(context.preprocessedFrameAssertions != PTRef_Undef);
    frameFormula = logic.mkAnd(context.preprocessedFrameAssertions, frameFormula);
    return preprocessFormula(frameFormula, context, {.skip = true});
}

vec<PTRef> MainSolver::preprocessFormulasPerPartition(vec<PTRef> const & frameFormulas,
                                                      PreprocessingContext const & context) {
    assert(context.perPartition);

    std::size_t const frameFormulasCount = frameFormulas.size();
    static_assert(std::is_unsigned_v<decltype(context.preprocessedFrameAssertionsCount)>);
    assert(context.preprocessedFrameAssertionsCount <= frameFormulasCount);
    std::size_t const formulasCountToProcess = frameFormulasCount - context.preprocessedFrameAssertionsCount;
    if (formulasCountToProcess == 0) { return {}; }

    vec<PTRef> processedFormulas;
    for (std::size_t i = context.preprocessedFrameAssertionsCount; i < frameFormulasCount; ++i) {
        PTRef fla = frameFormulas[i];
        PTRef processed = fla;
        processed = preprocessFormulaItes(processed, context);
        processed = preprocessFormulaBeforeFinalTheoryPreprocessing(processed, context);
        processedFormulas.push(processed);
    }

    preprocessedAssertionsCount += processedFormulas.size();

    assert(std::size_t(processedFormulas.size()) == formulasCountToProcess);
    assert(std::size_t(processedFormulas.size()) > 0);
    if (std::all_of(processedFormulas.begin(), processedFormulas.end(),
                    [&](PTRef fla) { return fla == logic.getTerm_true(); })) {
        return {};
    }

    preprocessFormulaDoFinalTheoryPreprocessing(context);

    for (PTRef & fla : processedFormulas) {
        if (fla == logic.getTerm_true()) { continue; }
        fla = preprocessFormulaAfterFinalTheoryPreprocessing(fla, context);
    }

    return processedFormulas;
}

PTRef MainSolver::preprocessFormulaItes(PTRef fla, PreprocessingContext const & context,
                                        PreprocessFormulaItesConfig const & conf) {
    if (conf.skip) { return fla; }
    return preprocessFormulaItesImpl(fla, context);
}

PTRef MainSolver::preprocessFormulaItesImpl(PTRef fla, PreprocessingContext const & context) {
    assert(fla != PTRef_Undef);

    bool const perPartition = context.perPartition;

    std::size_t const partitionNumber = perPartition ? pmanager.getPartitionIndex(fla) : preprocessedAssertionsCount;
    PTRef processed = IteHandler(logic, partitionNumber).rewrite(fla);
    assert(processed != PTRef_Undef);
    if (perPartition) { pmanager.transferPartitionMembership(fla, processed); }
    return processed;
}

PTRef MainSolver::preprocessFormula(PTRef fla, PreprocessingContext const & context,
                                    PreprocessFormulaItesConfig const & iteConfig) {
    PTRef processed = fla;
    processed = preprocessFormulaItes(processed, context, iteConfig);
    processed = preprocessFormulaBeforeFinalTheoryPreprocessing(processed, context);
    preprocessFormulaDoFinalTheoryPreprocessing(context);
    processed = preprocessFormulaAfterFinalTheoryPreprocessing(processed, context);
    return processed;
}

PTRef MainSolver::preprocessFormulaBeforeFinalTheoryPreprocessing(PTRef fla, PreprocessingContext const & context) {
    bool const perPartition = context.perPartition;
    PTRef processed = fla;

    if (not perPartition) {
        if (context.frameCount > 0) { processed = applyLearntSubstitutions(processed); }
        processed = theory->preprocessBeforeSubstitutions(processed, context);
        processed = substitutionPass(processed, context);
    }

    processed = theory->preprocessAfterSubstitutions(processed, context);

    if (perPartition) {
        pmanager.transferPartitionMembership(fla, processed);
    } else if (logic.isFalse(processed)) {
        return logic.getTerm_false();
    }

    preprocessor.addPreprocessedFormula(processed);

    return processed;
}

void MainSolver::preprocessFormulaDoFinalTheoryPreprocessing(PreprocessingContext const &) {
    theory->afterPreprocessing(preprocessor.getPreprocessedFormulas());
}

PTRef MainSolver::preprocessFormulaAfterFinalTheoryPreprocessing(PTRef fla, PreprocessingContext const & context) {
    bool const perPartition = context.perPartition;
    PTRef processed = fla;

    assert(not perPartition or pmanager.getPartitionIndex(processed) != -1);

    // Optimize the dag for cnfization
    if (logic.isBooleanOperator(processed)) {
        processed = rewriteMaxArity(processed);
        if (perPartition) { pmanager.transferPartitionMembership(fla, processed); }
    }

    if (perPartition) {
        assert(pmanager.getPartitionIndex(processed) != -1);
        pmanager.propagatePartitionMask(processed);
    }

    return processed;
}

vec<PTRef> MainSolver::getCurrentAssertions() const {
    vec<PTRef> assertions;
    size_t const cnt = frames.frameCount();
    for (size_t i = 0; i < cnt; ++i) {
        for (PTRef fla : frames[i].formulas) {
            assertions.push(fla);
        }
    }
    return assertions;
}

vec<PTRef> const & MainSolver::getAssertionsAtLevel(std::size_t level) const {
    assert(level <= getAssertionLevel());
    return frames[level].formulas;
}

void MainSolver::printCurrentAssertionsAsQuery() const {
    char * base_name = config.dump_query_name();
    if (base_name == NULL)
        printCurrentAssertionsAsQuery(std::cout);
    else {
        char * s_file_name;
        int chars_written = asprintf(&s_file_name, "%s-%d.smt2", base_name, check_called);
        (void)chars_written;
        std::ofstream stream;
        stream.open(s_file_name);
        printCurrentAssertionsAsQuery(stream);
        stream.close();
        free(s_file_name);
    }
    free(base_name);
}

void MainSolver::printCurrentAssertionsAsQuery(std::ostream & s) const {
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
    printResolutionProofSMT2(std::cout);
}

void MainSolver::printResolutionProofSMT2(std::ostream & os) const {
    assert(smt_solver);
    if (!smt_solver->logsResolutionProof()) { throw ApiException("Proofs are not tracked"); }
    if (status != s_False) { throw ApiException("Proof cannot be created if solver is not in UNSAT state"); }

    return smt_solver->printResolutionProofSMT2(os);
}

std::unique_ptr<UnsatCore> MainSolver::getUnsatCore() const {
    if (not config.produce_unsat_cores()) { throw ApiException("Producing unsat cores is not enabled"); }
    if (status != s_False) { throw ApiException("Unsat core cannot be extracted if solver is not in UNSAT state"); }

    UnsatCoreBuilder unsatCoreBuilder{*this};

    return unsatCoreBuilder.build();
}

lbool MainSolver::getTermValue(PTRef tr) const {
    // TODO: implement also getAssignment (move from Interpret) where it would not check these for every particular term
    if (not config.produce_assignments()) { throw ApiException("Producing assignments is not enabled"); }
    if (status != s_True) { throw ApiException("Assignment cannot be created if solver is not in SAT state"); }

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

sstat MainSolver::giveToSolver(PTRef root, FrameId push_id) {

    struct ClauseCallBack : public Cnfizer::ClauseCallBack {
        std::vector<vec<Lit>> clauses;
        void operator()(vec<Lit> && c) override { clauses.push_back(std::move(c)); }
    };

    if (root == logic.getTerm_true()) { return s_Undef; }

    ClauseCallBack callBack;
    ts.setClauseCallBack(&callBack);
    ts.Cnfizer::cnfize(root, push_id);
    bool const keepPartitionsSeparate = trackPartitions();
    Lit frameLit;
    if (push_id != 0) { frameLit = term_mapper->getOrCreateLit(frameTerms[push_id]); }
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

    if (config.dump_query()) printCurrentAssertionsAsQuery();

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
    assert(not trackPartitions());
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
    logic.substitutionsTransitiveClosure(allsubsts);
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
