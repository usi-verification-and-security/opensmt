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


class MainSolver
{
public:
    struct FrameId
    {
        uint32_t id;
        bool operator== (const FrameId other) const { return id == other.id; }
        bool operator!= (const FrameId other) const { return id != other.id; }
    };

protected:
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
        explicit PushFrame(uint32_t id) : id({id}), unsat(false) {}
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

    std::unique_ptr<Theory>         theory;
    std::unique_ptr<TermMapper>     term_mapper;
    std::unique_ptr<THandler>       thandler;
    std::unique_ptr<SimpSMTSolver>  smt_solver;
    Logic&                          logic;
    PartitionManager                pmanager;
    SMTConfig&                      config;
    Tseitin                         ts;
    AssertionStack                  frames;
    vec<PTRef> frameTerms;

    std::size_t firstNotSimplifiedFrame = 0;



    opensmt::OSMTTimeVal query_timer; // How much time we spend solving.
    std::string          solver_name; // Name for the solver
    int            check_called = 0;     // A counter on how many times check was called.
    sstat          status = s_Undef;  // The status of the last solver call
    unsigned int   inserted_formulas_count = 0; // Number of formulas that has been inserted to this solver

    sstat solve();

    virtual sstat solve_(vec<FrameId> const & enabledFrames);

    sstat giveToSolver(PTRef root, FrameId push_id);

    PTRef rewriteMaxArity(PTRef);

    [[nodiscard]] PTRef currentRootInstance() const;

    // helper private methods
    PTRef newFrameTerm(FrameId frameId);
    bool isLastFrameUnsat() const { return frames.last().unsat; }
    void rememberLastFrameUnsat() { frames.last().unsat = true; }
    void rememberUnsatFrame(std::size_t frameIndex) {
        assert(frameIndex < frames.frameCount());
        for (; frameIndex < frames.frameCount(); ++frameIndex) {
            frames[frameIndex].unsat = true;
        }
    }

    void printFramesAsQuery(std::ostream & s) const
    {
        logic.dumpHeaderToFile(s);
        for (std::size_t i = 0; i < frames.frameCount(); ++i) {
            if (i > 0)
                s << "(push 1)\n";
            for (PTRef assertion : frames[i].formulas) {
                logic.dumpFormulaToFile(s, assertion);
            }
        }
        logic.dumpChecksatToFile(s);
    }

    static std::unique_ptr<SimpSMTSolver> createInnerSolver(SMTConfig& config, THandler& thandler);


  public:

    MainSolver(Logic& logic, SMTConfig& conf, std::string name)
            :
            theory(createTheory(logic, conf)),
            term_mapper(new TermMapper(logic)),
            thandler(new THandler(getTheory(), *term_mapper)),
            smt_solver(createInnerSolver(conf, *thandler)),
            logic(thandler->getLogic()),
            pmanager(logic),
            config(conf),
            ts(logic, *term_mapper),
            solver_name {std::move(name)}
    {
        conf.setUsedForInitiliazation();
        // Special handling of zero-level frame
        frames.push();
        frameTerms.push(logic.getTerm_true());
        initialize();
    }

    MainSolver(std::unique_ptr<Theory> th, std::unique_ptr<TermMapper> tm, std::unique_ptr<THandler> thd,
               std::unique_ptr<SimpSMTSolver> ss, Logic & logic, SMTConfig & conf, std::string name)
            :
            theory(std::move(th)),
            term_mapper(std::move(tm)),
            thandler(std::move(thd)),
            smt_solver(std::move(ss)),
            logic(thandler->getLogic()),
            pmanager(logic),
            config(conf),
            ts(logic,*term_mapper),
            solver_name {std::move(name)}
    {
        conf.setUsedForInitiliazation();
        frames.push();
        frameTerms.push(logic.getTerm_true());
        initialize();
    }

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
    PartitionManager &getPartitionManager() { return pmanager; }
    void      push();
    bool      pop();
    void      insertFormula(PTRef fla);

    void      initialize();

    virtual sstat check();      // A wrapper for solve which simplifies the loaded formulas and initializes the solvers
    // Simplify frames (not yet simplified) until all are simplified or the instance is detected unsatisfiable.
    sstat simplifyFormulas();

    void  printFramesAsQuery() const;
    sstat getStatus       () const { return status; }

    // Values
    lbool   getTermValue   (PTRef tr) const;

    // Returns model of the last query (must be in satisfiable state)
    std::unique_ptr<Model> getModel();

    void stop() { smt_solver->stop = true; }

    // Returns interpolation context for the last query (must be in UNSAT state)
    std::unique_ptr<InterpolationContext> getInterpolationContext();

    static std::unique_ptr<Theory> createTheory(Logic & logic, SMTConfig & config);
};

#endif // MAINSOLVER_H
