/*
 *  Copyright (c) 2012 - 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2022 - 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef MAINSOLVER_H
#define MAINSOLVER_H


#include "Tseitin.h"
#include "SimpSMTSolver.h"
#include "Model.h"
#include "PartitionManager.h"
#include "InterpolationContext.h"

#include <memory>


class Logic;

class sstat {
    char value;
  public:
    explicit sstat(int v) : value(v) {}
    bool operator == (sstat s) const { return value == s.value; }
    bool operator != (sstat s) const { return value != s.value; }
    sstat() : value(0) {}
    sstat(lbool l) {
        if (l == l_True)
            value = 1;
        else if (l == l_False)
            value = -1;
        else if (l == l_Undef)
            value = 0;
        else assert(false);
    }
    char getValue()            const { return value; }
    friend sstat toSstat(int v);
};

inline sstat toSstat(int v) {return sstat(v); }

const sstat s_True  = toSstat( 1);
const sstat s_False = toSstat(-1);
const sstat s_Undef = toSstat( 0);
const sstat s_Error = toSstat( 2);


class MainSolver {
protected: /** Helper classes to deal with assertion stack, preprocessing and substitutions **/
    using FrameId = uint32_t;

    struct PushFrame {
    private:
        FrameId id;

    public:
        FrameId getId() const { return id; }
        int size() const { return formulas.size(); }
        void push(PTRef tr) { formulas.push(tr); }
        PTRef operator[](int i) const { return formulas[i]; }
        vec<PTRef> formulas;
        bool unsat; // If true then the stack of frames with this frame at top is UNSAT

        PushFrame(PushFrame const &) = delete;
        PushFrame(PushFrame &&) = default;
        explicit PushFrame(uint32_t id) : id(id), unsat(false) {}
    };

    class AssertionStack {
    private:
        std::vector<PushFrame> frames;
        uint32_t frameId = 0;

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
    };

    class Substitutions {
        std::vector<Logic::SubstMap> perFrameSubst;

    public:
        void push() { perFrameSubst.emplace_back(); }
        void pop() { perFrameSubst.pop_back(); }

        void set(std::size_t level, Logic::SubstMap && subs) {
            perFrameSubst.at(level) = std::move(subs);
        }

        Logic::SubstMap current() {
            Logic::SubstMap allSubst;
            for (auto const & subs : perFrameSubst) {
                for (PTRef key : subs.getKeys()) {
                    assert(not allSubst.has(key));
                    allSubst.insert(key, subs[key]);
                }
            }
            return allSubst;
        }
    };
/** Actual MainSolver members **/
protected:
    AssertionStack frames;
    Substitutions substitutions;
    vec<PTRef> frameTerms;
    std::size_t firstNotSimplifiedFrame = 0;
    unsigned int insertedFormulasCount = 0;
    sstat status = s_Undef;  // The status of the last solver call

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

    PTRef rewriteMaxArity(PTRef root);

    virtual sstat solve_(vec<FrameId> const & enabledFrames);

    sstat giveToSolver(PTRef root, FrameId push_id);

    struct SubstitutionResult {
        Logic::SubstMap usedSubstitution;
        PTRef result {PTRef_Undef};
    };

    PTRef applyLearntSubstitutions(PTRef fla);

    PTRef substitutionPass(PTRef fla, PreprocessingContext const& context);

    SubstitutionResult computeSubstitutions(PTRef fla);

public:
    std::unique_ptr<Theory>         theory;
    std::unique_ptr<TermMapper>     term_mapper;
    std::unique_ptr<THandler>       thandler;
    std::unique_ptr<SimpSMTSolver>  smt_solver;
    Logic&                          logic;
    PartitionManager                pmanager;
    SMTConfig&                      config;
    Tseitin                         ts;

    opensmt::OSMTTimeVal query_timer; // How much time we spend solving.
    std::string          solver_name; // Name for the solver
    int            check_called = 0;     // A counter on how many times check was called.

    sstat solve();

    [[nodiscard]] PTRef currentRootInstance() const;

    void printFramesAsQuery(std::ostream & s) const;

    static std::unique_ptr<SimpSMTSolver> createInnerSolver(SMTConfig& config, THandler& thandler);

    MainSolver(Logic& logic, SMTConfig& conf, std::string name);

    MainSolver(std::unique_ptr<Theory> th, std::unique_ptr<TermMapper> tm, std::unique_ptr<THandler> thd,
               std::unique_ptr<SimpSMTSolver> ss, Logic & logic, SMTConfig & conf, std::string name);

    virtual ~MainSolver() = default;
    MainSolver             (const MainSolver&) = delete;
    MainSolver& operator = (const MainSolver&) = delete;
    MainSolver             (MainSolver&&) = default;
    MainSolver& operator = (MainSolver&&) = delete;

    SMTConfig& getConfig() { return config; }
    SimpSMTSolver & getSMTSolver() { return *smt_solver; }
    SimpSMTSolver const & getSMTSolver() const { return *smt_solver; }

    THandler &getTHandler() { return *thandler; }
    Logic    &getLogic()    { return logic; }
    Theory   &getTheory()   { return *theory; }
    const Theory &getTheory() const { return *theory; }
    PartitionManager & getPartitionManager();

    void      push();
    bool      pop();
    void      insertFormula(PTRef fla);

    void      initialize();

    virtual sstat check();      // A wrapper for solve which simplifies the loaded formulas and initializes the solvers
    // Simplify frames (not yet simplified) until all are simplified or the instance is detected unsatisfiable.
    sstat simplifyFormulas();

    void  printFramesAsQuery() const;
    [[nodiscard]] sstat getStatus() const;

    // Values
    lbool   getTermValue   (PTRef tr) const;

    // Returns model of the last query (must be in satisfiable state)
    std::unique_ptr<Model> getModel();

    void stop() { smt_solver->stop = true; }

    // Returns interpolation context for the last query (must be in UNSAT state)
    std::unique_ptr<InterpolationContext> getInterpolationContext();

    static std::unique_ptr<Theory> createTheory(Logic & logic, SMTConfig & config);
};

bool MainSolver::trackPartitions() const
{
    assert(smt_solver);
    return smt_solver->logsResolutionProof();
}

#endif // MAINSOLVER_H
