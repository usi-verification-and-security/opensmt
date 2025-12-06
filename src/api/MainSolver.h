/*
 *  Copyright (c) 2012 - 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2022 - 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef MAINSOLVER_H
#define MAINSOLVER_H

#include "PartitionManager.h"

#include <cnfizers/Tseitin.h>
#include <common/ScopedVector.h>
#include <common/TermNames.h>
#include <models/Model.h>
#include <proof/InterpolationContext.h>
#include <smtsolvers/SimpSMTSolver.h>
#include <unsatcores/UnsatCore.h>

#include <memory>

namespace opensmt {
class Logic;

class sstat {
public:
    explicit sstat(int v) : value(v) {}
    bool operator==(sstat s) const { return value == s.value; }
    bool operator!=(sstat s) const { return value != s.value; }
    sstat() : value(0) {}
    sstat(lbool l) {
        if (l == l_True)
            value = 1;
        else if (l == l_False)
            value = -1;
        else if (l == l_Undef)
            value = 0;
        else
            assert(false);
    }
    char getValue() const { return value; }
    friend sstat toSstat(int v);

private:
    char value;
};

inline sstat toSstat(int v) {
    return sstat(v);
}

sstat const s_True = toSstat(1);
sstat const s_False = toSstat(-1);
sstat const s_Undef = toSstat(0);
sstat const s_Error = toSstat(2);

class MainSolver {
public:
    MainSolver(Logic & logic, SMTConfig & conf, std::string name);

    MainSolver(std::unique_ptr<Theory> th, std::unique_ptr<TermMapper> tm, std::unique_ptr<THandler> thd,
               std::unique_ptr<SimpSMTSolver> ss, Logic & logic, SMTConfig & conf, std::string name);

    virtual ~MainSolver() = default;
    MainSolver(MainSolver const &) = delete;
    MainSolver & operator=(MainSolver const &) = delete;
    MainSolver(MainSolver &&) = default;
    MainSolver & operator=(MainSolver &&) = delete;

    SMTConfig & getConfig() const { return config; }
    Logic & getLogic() const { return logic; }

    SimpSMTSolver & getSMTSolver() { return *smt_solver; }
    SimpSMTSolver const & getSMTSolver() const { return *smt_solver; }

    THandler & getTHandler() { return *thandler; }
    THandler const & getTHandler() const { return *thandler; }

    // Increases/decreases the level of the assertion stack [1]
    // [1]: The SMT-LIB Standard: Version 2.6, section 4.1.4
    // https://smt-lib.org/language.shtml
    void push();
    bool pop();
    // The current assertion level; the first assertion level is 0
    std::size_t getAssertionLevel() const;

    void insertFormula(PTRef fla);
    // Alias for `insertFormula`, reserved for future use
    void addAssertion(PTRef fla) { return insertFormula(fla); }
    std::size_t getInsertedFormulasCount() const { return insertedAssertionsCount; }
    // Alias for `getInsertedFormulasCount`, reserved for future use
    std::size_t getAssertionsCount() const { return getInsertedFormulasCount(); }

    // Uses tryAddTermName and inserts the formula only on success
    bool tryAddNamedAssertion(PTRef, std::string const & name);
    // Try add a unique name for a term already included in the assertions
    bool tryAddTermNameFor(PTRef, std::string const & name);

    void initialize();

    virtual sstat check(); // A wrapper for solve which simplifies the loaded formulas and initializes the solvers
    sstat solve();
    // Simplify formulas until all are simplified or the instance is detected unsat
    // Skip assertion levels that have already been simplified
    sstat simplifyFormulas();
    // Alias for `simplifyFormulas`, reserved for future use
    sstat preprocess() { return simplifyFormulas(); }

    [[nodiscard]] sstat getStatus() const { return status; }

    // Returns a copy of all assertions of the currently valid assertion levels of the the assertion stack
    // I.e., *excluding* popped assertions
    vec<PTRef> getCurrentAssertions() const;
    // Returns just a view to the assertions
    auto getCurrentAssertionsView() const { return getCurrentAssertionsViewImpl(); }

    vec<PTRef> const & getAssertionsAtCurrentLevel() const { return getAssertionsAtLevel(getAssertionLevel()); }
    vec<PTRef> const & getAssertionsAtLevel(std::size_t) const;

    [[deprecated("Use printCurrentAssertionsAsQuery")]]
    void printFramesAsQuery() const {
        printCurrentAssertionsAsQuery();
    }
    void printCurrentAssertionsAsQuery() const;
    void printCurrentAssertionsAsQuery(std::ostream &) const;

    // Values
    lbool getTermValue(PTRef tr) const;

    // Returns model of the last query (must be in satisfiable state)
    std::unique_ptr<Model> getModel();

    std::unique_ptr<UnsatCore> getUnsatCore() const;

    // Prints proof of the last query (must be in unsatisfiable state)
    void printResolutionProofSMT2() const;
    void printResolutionProofSMT2(std::ostream &) const;

    // Returns interpolation context for the last query (must be in UNSAT state)
    std::unique_ptr<InterpolationContext> getInterpolationContext();

    [[deprecated("Use tryAddNamedAssertion or tryAddTermNameFor")]]
    TermNames & getTermNames() {
        return termNames;
    }
    TermNames const & getTermNames() const { return termNames; }

    // Notify this particular solver to stop the computation
    // For stopping at the global scope, refer to GlobalStop.h
    void notifyStop() { smt_solver->notifyStop(); }

    static std::unique_ptr<Theory> createTheory(Logic & logic, SMTConfig & config);

protected:
    friend class UnsatCoreBuilderBase;

    using FrameId = uint32_t;

    struct PushFrame {
    public:
        FrameId getId() const { return id; }
        int size() const { return formulas.size(); }
        void push(PTRef tr) { formulas.push(tr); }
        PTRef operator[](int i) const { return formulas[i]; }
        vec<PTRef> formulas;
        bool unsat{false}; // If true then the stack of frames with this frame at top is UNSAT

        PushFrame(PushFrame const &) = delete;
        PushFrame & operator=(PushFrame const &) = delete;
        PushFrame(PushFrame &&) = default;
        PushFrame & operator=(PushFrame &&) = default;
        explicit PushFrame(uint32_t id) : id(id) {}

    private:
        FrameId id;
    };

    class AssertionStack {
    public:
        [[nodiscard]] PushFrame const & last() const {
            assert(not frames.empty());
            return frames.back();
        }
        [[nodiscard]] PushFrame & last() {
            assert(not frames.empty());
            return frames.back();
        }

        [[nodiscard]] std::size_t frameCount() const { return frames.size(); }

        PushFrame const & operator[](std::size_t i) const {
            assert(i < frames.size());
            return frames[i];
        }
        PushFrame & operator[](std::size_t i) {
            assert(i < frames.size());
            return frames[i];
        }

        void push() { frames.emplace_back(frameId++); }

        void pop() { frames.pop_back(); }

        void add(PTRef fla) {
            assert(frameCount() > 0);
            last().push(fla);
        }

    private:
        std::vector<PushFrame> frames;
        uint32_t frameId = 0;
    };

    struct SubstitutionResult {
        Logic::SubstMap usedSubstitution;
        PTRef result{PTRef_Undef};
    };

    class Preprocessor {
    public:
        void push();
        void pop();
        void initialize();
        void addPreprocessedFormula(PTRef);
        [[nodiscard]] span<PTRef const> getPreprocessedFormulas() const;
        [[nodiscard]] Logic::SubstMap getCurrentSubstitutions() const { return substitutions.current(); }
        void setSubstitutions(std::size_t level, Logic::SubstMap && subs) { substitutions.set(level, std::move(subs)); }
        void prepareForProcessingFrame(std::size_t frameIndex);

    private:
        class Substitutions {
        public:
            void push() { perFrameSubst.emplace_back(); }
            void pop() { perFrameSubst.pop_back(); }

            void set(std::size_t level, Logic::SubstMap && subs) { perFrameSubst.at(level) = std::move(subs); }

            [[nodiscard]] Logic::SubstMap current() const {
                Logic::SubstMap allSubst;
                for (auto const & subs : perFrameSubst) {
                    for (PTRef key : subs.getKeys()) {
                        assert(not allSubst.has(key));
                        allSubst.insert(key, subs[key]);
                    }
                }
                return allSubst;
            }

        private:
            std::vector<Logic::SubstMap> perFrameSubst;
        };

        void pushInternal();
        void popInternal();

        Substitutions substitutions;
        ScopedVector<PTRef> preprocessedFormulas;
        std::size_t solverFrameCount{1};
        std::size_t internalFrameCount{1};
    };

    Theory & getTheory() { return *theory; }
    Theory const & getTheory() const { return *theory; }
    TermMapper & getTermMapper() const { return *term_mapper; }
    PartitionManager & getPartitionManager() { return pmanager; }

    // TODO: inefficient
    vec<PTRef> getCurrentAssertionsViewImpl() const { return getCurrentAssertions(); }

    static std::unique_ptr<SimpSMTSolver> createInnerSolver(SMTConfig & config, THandler & thandler);

    PTRef newFrameTerm(FrameId frameId) {
        assert(frameId != 0);
        auto name = std::string(Logic::s_framev_prefix) + std::to_string(frameId);
        PTRef frameTerm = logic.mkBoolVar(name.c_str());
        Lit l = term_mapper->getOrCreateLit(frameTerm);
        term_mapper->setFrozen(var(l));
        smt_solver->addAssumptionVar(var(l));
        return frameTerm;
    }
    bool isLastFrameUnsat() const { return frames.last().unsat; }
    void rememberLastFrameUnsat() { frames.last().unsat = true; }
    void rememberUnsatFrame(std::size_t frameIndex) {
        assert(frameIndex < frames.frameCount());
        for (; frameIndex < frames.frameCount(); ++frameIndex) {
            frames[frameIndex].unsat = true;
        }
    }

    inline bool trackPartitions() const;

    virtual bool tryPreprocessFormulasOfFrame(std::size_t);

    virtual PTRef preprocessFormulasDefault(vec<PTRef> const & frameFormulas, PreprocessingContext const &);
    virtual vec<PTRef> preprocessFormulasPerPartition(vec<PTRef> const & frameFormulas, PreprocessingContext const &);

    virtual PTRef preprocessFormula(PTRef, PreprocessingContext const &);
    virtual PTRef preprocessFormulaBeforeFinalTheoryPreprocessing(PTRef, PreprocessingContext const &);
    virtual void preprocessFormulaDoFinalTheoryPreprocessing(PreprocessingContext const &);
    virtual PTRef preprocessFormulaAfterFinalTheoryPreprocessing(PTRef, PreprocessingContext const &);

    PTRef rewriteMaxArity(PTRef root);

    virtual sstat solve_(vec<FrameId> const & enabledFrames);

    sstat giveToSolver(PTRef root, FrameId push_id);

    PTRef applyLearntSubstitutions(PTRef fla);

    PTRef substitutionPass(PTRef fla, PreprocessingContext const & context);

    SubstitutionResult computeSubstitutions(PTRef fla);

    AssertionStack frames;

    sstat status = s_Undef; // The status of the last solver call

private:
    std::unique_ptr<Theory> theory;
    std::unique_ptr<TermMapper> term_mapper;
    std::unique_ptr<THandler> thandler;
    std::unique_ptr<SimpSMTSolver> smt_solver;
    TermNames termNames;
    Logic & logic;
    PartitionManager pmanager;
    SMTConfig & config;
    Tseitin ts;
    Preprocessor preprocessor;

    TimeVal query_timer;     // How much time we spend solving.
    std::string solver_name; // Name for the solver
    int check_called = 0;    // A counter on how many times check was called.

    vec<PTRef> frameTerms;
    std::size_t firstNotPreprocessedFrame = 0;
    std::size_t insertedAssertionsCount = 0;
};

bool MainSolver::trackPartitions() const {
    assert(smt_solver);

    if (smt_solver->logsResolutionProof()) { return true; }
    if (config.produce_assignments()) { return true; }
    // Even if computed independently of resolution proofs, we must track partitions
    if (config.produce_unsat_cores()) { return true; }
    if (config.produce_inter()) { return true; }

    return false;
}
} // namespace opensmt

#endif // MAINSOLVER_H
