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
#include "CnfState.h"
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
    formulas.push(pfstore.alloc());
}

bool
MainSolver::pop()
{
    if (formulas.size() > 1) {
        formulas.pop();
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
    int partition_index = inserted_formulas_count++;
#ifdef PRODUCE_PROOF
    logic.assignPartition(partition_index, root);
    assert(logic.getPartitionIndex(root) != -1);
    PTRef old_root = root;
#endif

    logic.conjoinExtras(root, root);

    #ifdef PRODUCE_PROOF
    logic.transferPartitionMembership(old_root, root);
    assert(logic.getPartitionIndex(root) != -1);
#endif // PRODUCE_PROOF

    pfstore[formulas.last()].push(root);
    pfstore[formulas.last()].units.clear();
    pfstore[formulas.last()].root = PTRef_Undef;
    pfstore[formulas.last()].substs = logic.getTerm_true();
    simplified_until = std::min(simplified_until, formulas.size()-1);
    return s_Undef;
}

sstat MainSolver::simplifyFormulas(int from, int& to, char** err_msg)
{
    if (binary_init)
        return s_Undef;


    status = s_Undef;

    vec<PTRef> coll_f;
    for (int i = from ; i < formulas.size(); i++) {
        bool res = getTheory().simplify(formulas, i);
        to = i+1;
        const PushFrame & frame = pfstore[formulas[i]];
        PTRef root = frame.root;

        if (logic.isFalse(root)) {
            giveToSolver(getLogic().getTerm_false(), frame.getId());
            return status = s_False;
        }
#ifdef PRODUCE_PROOF
        assert(frame.substs == logic.getTerm_true());
        vec<PTRef> const & flas =  frame.formulas;
        for (int j = 0; j < flas.size(); ++j) {
            PTRef fla = flas[j];
            if (fla == logic.getTerm_true()) {continue;}
            assert(logic.getPartitionIndex(fla) != -1);
            // Optimize the dag for cnfization
            if (logic.isBooleanOperator(fla)) {
                PTRef old = fla;
                Map<PTRef,int,PTRefHash> PTRefToIncoming;
                computeIncomingEdges(fla, PTRefToIncoming);
                fla = rewriteMaxArity(fla, PTRefToIncoming);
                logic.transferPartitionMembership(old, fla);
            }
            assert(logic.getPartitionIndex(fla) != -1);
            logic.computePartitionMasks(fla);
            if ((status = giveToSolver(fla, frame.getId())) == s_False) {
                return s_False;
            }
        }
#else // PRODUCE_PROOF
        FContainer fc(root);

        // Optimize the dag for cnfization
        Map<PTRef,int,PTRefHash> PTRefToIncoming;
        if (logic.isBooleanOperator(fc.getRoot())) {
            computeIncomingEdges(fc.getRoot(), PTRefToIncoming);
            PTRef flat_root = rewriteMaxArity(fc.getRoot(), PTRefToIncoming);
            fc.setRoot(flat_root);
        }

        // root_instance is updated to the and of the simplified formulas currently in the solver, together with the substitutions
        fc.setRoot(logic.mkAnd(fc.getRoot(), pfstore[formulas[i]].substs));
        root_instance.setRoot(fc.getRoot());
        // Stop if problem becomes unsatisfiable
        if ((status = giveToSolver(fc.getRoot(), pfstore[formulas[i]].getId())) == s_False)
            break;
#endif
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
void MainSolver::computeIncomingEdges(PTRef tr, Map<PTRef,int,PTRefHash>& PTRefToIncoming)
{
    ::computeIncomingEdges(logic, tr, PTRefToIncoming);
}

PTRef MainSolver::rewriteMaxArity(PTRef root, const Map<PTRef,int,PTRefHash>& PTRefToIncoming)
{
    return ::rewriteMaxArity(logic, root, PTRefToIncoming);
}

PTRef MainSolver::mergePTRefArgs(PTRef tr, Map<PTRef,PTRef,PTRefHash>& cache, const Map<PTRef,int,PTRefHash>& PTRefToIncoming)
{
    return ::mergePTRefArgs(logic, tr, cache, PTRefToIncoming);
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
        return ValPair(tr, val == l_True ? "true" : (val == l_False ? "false" : "unknown"));
    } else {
        ValPair vp = thandler.getValue(tr);
        if (vp.val == NULL)
            vp.val = strdup(logic.getDefaultValue(tr));
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
        splits[i].constraintsToPTRefs(constraints);
        addToConj(constraints, conj_vec);

        vec<vec<PtAsgn> > learnts;
        splits[i].learntsToPTRefs(learnts);
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
        getTheory().printFramesAsQuery(formulas, std::cout);
    else {
        char* s_file_name;
        int chars_written = asprintf(&s_file_name, "%s-%d.smt2", base_name, check_called);
        (void)chars_written;
        std::ofstream stream;
        stream.open(s_file_name);
        getTheory().printFramesAsQuery(formulas, stream);
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
    sstat rval;
    int simplified_to;
    rval = simplifyFormulas(simplified_until, simplified_to);

    simplified_until = simplified_to;
    if (config.dump_query())
        printFramesAsQuery();

    if (rval != s_Undef)
        return rval;
    initialize();
    return solve();
}

sstat MainSolver::solve()
{
    if (!smt_solver->okay())
        return s_False;

    if (config.sat_split_type() == spt_lookahead) {
        int fix_vars;
        if (config.sat_split_fixvars() > 0)
            fix_vars = config.sat_split_fixvars();
            fix_vars = getLog2Ceil(config.sat_split_num());
        sstat res = lookaheadSplit(fix_vars);
        return res;
    }
    else if (config.sat_pure_lookahead()) {
        return lookaheadSplit(-1);
    }

    vec<PTRef> query;

    vec<FrameId> en_frames;
    for (int i = 0; i < formulas.size(); i++) {
        en_frames.push(pfstore[formulas[i]].getId());
        query.push(pfstore[formulas[i]].root);
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
    interp.parse_only = true;
    interp.interpFile(f);
    return true;
}

