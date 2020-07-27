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
#include "TreeOps.h"
#include "DimacsParser.h"
#include "Interpret.h"
#include "BoolRewriting.h"
#include <thread>
#include <random>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

namespace opensmt { extern bool stop; }
//#include "symmetry/Symmetry.h"

void
MainSolver::push()
{
    bool alreadyUnsat = isLastFrameUnsat();
    frames.push(pfstore.alloc());
    if (alreadyUnsat) { rememberLastFrameUnsat(); }
}

bool
MainSolver::pop()
{
    if (frames.size() > 1) {
        if (config.produce_inter() > 0) {
            auto toPop = frames.last();
            auto& partitionsToInvalidate = pfstore[toPop].formulas;
            ipartitions_t mask = 0;
            for (int i = 0; i < partitionsToInvalidate.size(); ++i) {
                PTRef part = partitionsToInvalidate[i];
                auto index = logic.getPartitionIndex(part);
                assert(index != -1);
                opensmt::setbit(mask, static_cast<unsigned int>(index));
            }
            logic.invalidatePartitions(mask);
        }
        frames.pop();
        if (!isLastFrameUnsat()) {
            getSMTSolver().restoreOK();
        }
        return true;
    }
    else
        return false;
}

sstat
MainSolver::push(PTRef root)
{

    push();
    char* msg;
    sstat res = insertFormula(root, &msg);
    if (res == s_Error)
        printf("%s\n", msg);
    return res;
}

sstat
MainSolver::insertFormula(PTRef root, char** msg)
{
    if (logic.getSortRef(root) != logic.getSort_bool())
    {
        int chars_written = asprintf(msg, "Top-level assertion sort must be %s, got %s",
                 Logic::s_sort_bool, logic.getSortName(logic.getSortRef(root)));
        (void)chars_written;
        return s_Error;
    }

    logic.conjoinExtras(root, root);
    if (getConfig().produce_inter()) {
        // MB: Important for HiFrog! partition index is the index of the formula in an virtual array of inserted formulas,
        //     thus we need the old value of count. TODO: Find a good interface for this so it cannot be broken this easily
        unsigned int partition_index = inserted_formulas_count++;
        logic.assignTopLevelPartitionIndex(partition_index, root);
        assert(logic.getPartitionIndex(root) != -1);
    }
    else {
        ++inserted_formulas_count;
    }

    PushFrame& lastFrame =  pfstore[frames.last()];
    lastFrame.push(root);
    lastFrame.units.clear();
    lastFrame.root = PTRef_Undef;
    lastFrame.substs = logic.getTerm_true();
    // New formula has been added to the last frame. If the frame has been simplified before, we need to do it again
    frames.setSimplifiedUntil(std::min(frames.getSimplifiedUntil(), frames.size() - 1));
    return s_Undef;
}

sstat MainSolver::simplifyFormulas(char** err_msg)
{
    if (binary_init)
        return s_Undef;


    status = s_Undef;

    vec<PTRef> coll_f;
    bool keepPartitionsSeparate = getConfig().produce_inter();
    // Process (and simplify) not yet processed frames. Stop processing if solver is in UNSAT state already
    for (std::size_t i = frames.getSimplifiedUntil(); i < frames.size() && status != s_False; i++) {
        getTheory().simplify(frames.getFrameReferences(), i);
        frames.setSimplifiedUntil(i + 1);
        const PushFrame & frame = pfstore[frames.getFrameReference(i)];

        if (keepPartitionsSeparate) {
            assert(frame.substs == logic.getTerm_true());
            vec<PTRef> const & flas = frame.formulas;
            for (int j = 0; j < flas.size() && status != s_False; ++j) {
                PTRef fla = flas[j];
                if (fla == logic.getTerm_true()) { continue; }
                assert(logic.getPartitionIndex(fla) != -1);
                // Optimize the dag for cnfization
                if (logic.isBooleanOperator(fla)) {
                    PTRef old = fla;
                    fla = rewriteMaxArity(fla);
                    logic.transferPartitionMembership(old, fla);
                }
                assert(logic.getPartitionIndex(fla) != -1);
                logic.propagatePartitionMask(fla);
                status = giveToSolver(fla, frame.getId());
            }
        } else {
            PTRef root = frame.root;
            if (logic.isFalse(root)) {
                giveToSolver(getLogic().getTerm_false(), frame.getId());
                status = s_False;
                break;
            }
            // Optimize the dag for cnfization
            if (logic.isBooleanOperator(root)) {
                root = rewriteMaxArity(root);
            }
            // root_instance is updated to the and of the simplified formulas currently in the solver, together with the substitutions
            root = logic.mkAnd(root, frame.substs);
            root_instance.setRoot(root);
            status = giveToSolver(root, frame.getId());
        }
    }
    if (status == s_False) {
        rememberUnsatFrame(frames.getSimplifiedUntil() - 1);
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

//
// Merge terms with shared signatures in egraph representation and remove redundancies in
// equalities and disequalities
//
MainSolver::FContainer MainSolver::simplifyEqualities(vec<PtChild>& terms)
{
#ifdef SIMPLIFY_DEBUG
    for (int i = 0; i < terms.size(); i++) {
        PtChild& ptc = terms[i];
        // XXX The terms in here might have invalid symbols for some reason.
//        assert(logic.hasSym(logic.getPterm(ptc.tr).symb()));
    }
#endif
    PTRef root = terms[terms.size()-1].tr;
    for (int i = 0; i < terms.size(); i++) {
        PtChild& ptc = terms[i];
        PTRef tr = ptc.tr;
        if (logic.isTheoryTerm(tr) && logic.getTerm_true() != tr && logic.getTerm_false() != tr) {
            if (logic.isEquality(tr)) {
                if (logic.simplifyEquality(ptc, true)) {
                    // the root of the formula is trivially true
                    root = logic.getTerm_true();
                    break;
                }

#ifdef SIMPLIFY_DEBUG
                if (ptc.parent != PTRef_Undef && tr != logic.getPterm(ptc.parent)[ptc.pos]) {
                    cerr << "Simplified equality " << logic.printTerm(tr) << endl;
                    cerr << "  " << logic.printTerm(logic.getPterm(ptc.parent)[ptc.pos]) << endl;
                }
#endif
            }
            else if (logic.isDisequality(tr)) {
//                cerr << "Simplifying disequality " << logic.printTerm(tr) << endl;
                logic.simplifyDisequality(ptc);
//                cerr << "  " << logic.printTerm(logic.getPterm(ptc.parent)[ptc.pos]) << endl;
            }
//            uf_solver.declareTerm(ptc);
        }
    }
    return FContainer(root);
}

ValPair MainSolver::getValue(PTRef tr) const
{
    if (logic.hasSortBool(tr)) {
        lbool val = ts.getTermValue(tr);
        if (val != l_Undef) {
            return ValPair(tr, val == l_True ? Logic::tk_true : Logic::tk_false);
        }
        // Try if it was not substituted away
        PTRef subs = thandler.getSubstitution(tr);
        if (subs != PTRef_Undef) {
            return getValue(subs);
        }
        // Term not seen in the formula, any value can be returned since it cannot have any effect on satisfiability
        return ValPair(tr, Logic::tk_true);

    } else {
        ValPair vp = thandler.getValue(tr);
        if (vp.val == nullptr) {
            vp.val = strdup(logic.getDefaultValue(tr));
        }
        return vp;
    }
}

void MainSolver::getValues(const vec<PTRef>& trs, vec<ValPair>& vals) const
{
    vals.clear();
    for (int i = 0; i < trs.size(); i++)
    {
        PTRef tr = trs[i];
        vals.push(getValue(tr));
    }
}

void MainSolver::addToConj(vec<vec<PtAsgn> >& in, vec<PTRef>& out)
{
    for (int i = 0; i < in.size(); i++) {
        vec<PtAsgn>& constr = in[i];
        vec<PTRef> disj_vec;
        for (int k = 0; k < constr.size(); k++)
            disj_vec.push(constr[k].sgn == l_True ? constr[k].tr : logic.mkNot(constr[k].tr));
        out.push(logic.mkOr(disj_vec));
    }
}

bool MainSolver::writeFuns_smtlib2(const char* file)
{
    std::ofstream file_s;
    file_s.open(file);
    if (file_s.is_open()) {
        logic.dumpFunctions(file_s);
        return true;
    }
    return false;
}

bool MainSolver::writeSolverState_smtlib2(const char* file, char** msg)
{
    char* name;
    int written = asprintf(&name, "%s.smt2", file);
    assert(written >= 0);
    std::ofstream file_s;
    file_s.open(name);
    if (file_s.is_open()) {
        logic.dumpHeaderToFile(file_s);
        logic.dumpFormulaToFile(file_s, root_instance.getRoot());
        logic.dumpChecksatToFile(file_s);
        file_s.close();
    }
    else {
        written = asprintf(msg, "Failed to open file %s\n", name);
        assert(written >= 0);
        free(name);
        return false;
    }
    (void)written;
    free(name);
    return true;
}

bool MainSolver::writeSolverSplits_smtlib2(const char* file, char** msg)
{
    vec<SplitData>& splits = ts.solver.splits;
    for (int i = 0; i < splits.size(); i++) {
        vec<PTRef> conj_vec;
        vec<vec<PtAsgn> > constraints;
        splits[i].constraintsToPTRefs(constraints, thandler);
        addToConj(constraints, conj_vec);

        vec<vec<PtAsgn> > learnts;
        splits[i].learntsToPTRefs(learnts, thandler);
        addToConj(learnts, conj_vec);

        if (config.smt_split_format_length() == spformat_full)
            conj_vec.push(root_instance.getRoot());

        PTRef problem = logic.mkAnd(conj_vec);

        char* name;
        int written = asprintf(&name, "%s-%02d.smt2", file, i);
        assert(written >= 0);
        (void)written;
        std::ofstream file;
        file.open(name);
        if (file.is_open()) {
            logic.dumpHeaderToFile(file);
            logic.dumpFormulaToFile(file, problem);

            if (config.smt_split_format_length() == spformat_full)
                logic.dumpChecksatToFile(file);

            file.close();
        }
        else {
            written = asprintf(msg, "Failed to open file %s\n", name);
            assert(written >= 0);
            free(name);
            return false;
        }
        free(name);
    }
    return true;
}

void MainSolver::printFramesAsQuery()
{
    char* base_name = config.dump_query_name();
    if (base_name == NULL)
        getTheory().printFramesAsQuery(frames.getFrameReferences(), std::cout);
    else {
        char* s_file_name;
        int chars_written = asprintf(&s_file_name, "%s-%d.smt2", base_name, check_called);
        (void)chars_written;
        std::ofstream stream;
        stream.open(s_file_name);
        getTheory().printFramesAsQuery(frames.getFrameReferences(), stream);
        stream.close();
        free(s_file_name);
    }
    free(base_name);
}

sstat MainSolver::check()
{
    check_called ++;
    if (config.timeQueries()) {
        printf("; %s query time so far: %f\n", solver_name.c_str(), query_timer.getTime());
        opensmt::StopWatch sw(query_timer);
    }
    if (isLastFrameUnsat()) {
        return s_False;
    }
    initialize();
    sstat rval = simplifyFormulas();

    if (config.dump_query())
        printFramesAsQuery();

    if (rval == s_Undef) {
        rval = solve();
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

    vec<FrameId> en_frames;
    for (std::size_t i = 0; i < frames.size(); i++) {
        const PushFrame& frame = pfstore[frames.getFrameReference(i)];
        en_frames.push(frame.getId());
    }
    status = sstat(ts.solve(en_frames));

    if (status == s_True && config.produce_models())
        thandler.computeModel();
    smt_solver->clearSearch();
    return status;
}

bool
MainSolver::readFormulaFromFile(const char *file)
{
    FILE *f;
    if((f = fopen(file, "rt")) == NULL)
    {
        //opensmt_error("can't open file");
        return false;
    }
    Interpret interp(config, &logic, &getTheory(), &thandler, smt_solver, this);
    interp.setParseOnly();
    interp.interpFile(f);
    return true;
}

