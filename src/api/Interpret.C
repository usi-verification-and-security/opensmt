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

#include <assert.h>
#include <stdarg.h>
#include <string.h>
#include <sstream>
#include <ctime>
#include <cstdlib>
#include <cassert>
#include <cstdio>
#include <readline/readline.h>
#include <readline/history.h>
#include "Interpret.h"
#include "Theory.h"
#include "UFLRATheory.h"
#include "Global.h"
#include "smt2tokens.h"
#include "MainSolver.h"

#ifdef ITP_DEBUG
#include "TreeOps.h"
#endif // ITP_DEBUG

namespace opensmt {
bool stop;
};

uint32_t LetFrame::id_cnt = 0;


/***********************************************************
 * Class defining interpreter
 ***********************************************************/

Interpret::~Interpret() {
    if(!parse_only)
    {
        if (thandler != NULL)
            delete thandler;
        if (main_solver != NULL)
            delete main_solver;
        if (theory != NULL)
            delete theory;
        if (solver != NULL)
            delete solver;
    }
}

void Interpret::new_solver() {
    this->solver = new SimpSMTSolver(this->config, *this->thandler);
}

PTRef
Interpret::getParsedFormula()
{
    PTRef root = logic->mkAnd(assertions);
    return root;
}

void Interpret::setInfo(ASTNode& n) {
    assert(n.getType() == UATTR_T || n.getType() == PATTR_T);

    char* name = NULL;
    if (n.getValue() == NULL) {
        ASTNode& an = **(n.children->begin());
        assert(an.getType() == UATTR_T || an.getType() == PATTR_T);
        name = strdup(an.getValue());
    }
    else // Normal option
        name = strdup(n.getValue());

    Info value(n);

    config.setInfo(name, value);
    free(name);
}

void Interpret::getInfo(ASTNode& n) {
    assert(n.getType() == INFO_T);

    const char* name;

    if (n.getValue() != NULL)
        name = n.getValue();
    else {
        assert(n.children != NULL);
        name = (**(n.children->begin())).getValue();
    }

    const Info& value = config.getInfo(name);

    if (value.isEmpty())
        notify_formatted(true, "no value for info %s", name);
    else {
        char* val_str = value.toString();
        notify_formatted(false, "%s %s", name, val_str);
        free(val_str);
    }
}

void Interpret::setOption(ASTNode& n) {
    assert(n.getType() == OPTION_T);
    char* name  = NULL;

    if (n.getValue() == NULL)  {
        // Attribute
        ASTNode& an = **(n.children->begin());
        assert(an.getType() == UATTR_T || an.getType() == PATTR_T);
        name = strdup(an.getValue());
    }
    else // Normal option
        name = strdup(n.getValue());

    SMTOption value(n);
    const char* msg = "ok";
    bool rval = config.setOption(name, value, msg);
    if (rval == false)
        notify_formatted(true, "set-option failed: %s", msg);
    free(name);
}

void Interpret::getOption(ASTNode& n) {
    assert(n.getType() == UATTR_T || n.getType() == PATTR_T );

    assert(n.getValue() != NULL);
    const char* name = n.getValue();

    const SMTOption& value = config.getOption(name);

    if (value.isEmpty())
        notify_formatted(true, "No value for attr %s", name);
    else {
        char* str_val = value.toString();
        notify_formatted(false, "%s",str_val);
        free(str_val);
    }
}

void Interpret::exit() {
    f_exit = true;
}

void Interpret::interp(ASTNode& n) {
    bool rval;
    assert(n.getType() == CMD_T);
    const smt2token cmd = n.getToken();
    switch (cmd.x) {
        case t_setlogic:
        {
            if(parse_only)
            {
                break;
            }
            ASTNode &logic_n = **(n.children->begin());
            const char* logic_name = logic_n.getValue();
            if (logic != NULL) {
                notify_formatted(true, "logic has already been set to %s", logic->getName());
            } else if (strcmp(logic_name, QF_UF.str) == 0) {
                UFTheory *uftheory = new UFTheory(config);
                theory = uftheory;
                thandler = new THandler(config, *uftheory);
                logic = &(theory->getLogic());
                //solver = new SimpSMTSolver(config, *thandler);
                new_solver();

                main_solver = new MainSolver(*thandler, config, solver, "qf_uf solver");
                main_solver->initialize();
            } else if (strcmp(logic_name, opensmt::QF_CUF.str) == 0) {
                CUFTheory *cuftheory = new CUFTheory(config);
                theory = cuftheory;
                thandler = new THandler(config, *cuftheory);
                logic = &(theory->getLogic());
                //solver = new SimpSMTSolver(config, *thandler);
                new_solver();

                main_solver = new MainSolver(*thandler, config, solver, "qf_cuf solver");
                main_solver->initialize();
            } else if ((strcmp(logic_name, QF_LRA.str) == 0) || (strcmp(logic_name, QF_RDL.str) == 0)) {
                LRATheory *lratheory = new LRATheory(config);
                theory = lratheory;
                thandler = new THandler(config, *lratheory);
                logic = &(theory->getLogic());

                //solver = new SimpSMTSolver(config, *thandler);
                new_solver();
                main_solver = new MainSolver(*thandler, config, solver, "qf_lra solver");
                main_solver->initialize();
            }
            else if ((strcmp(logic_name, QF_LIA.str) == 0) || (strcmp(logic_name, QF_RDL.str) == 0)) {
                LIATheory *liatheory = new LIATheory(config);
                theory = liatheory;
                thandler = new THandler(config, *liatheory);
                logic = &(theory->getLogic());

                //solver = new SimpSMTSolver(config, *thandler);
                new_solver();
                main_solver = new MainSolver(*thandler, config, solver, "qf_lia solver");
                main_solver->initialize();
            } else if ((strcmp(logic_name, QF_UFLRA.str) == 0) || (strcmp(logic_name, QF_UFRDL.str) == 0)) {
                    UFLRATheory* uflratheory = new UFLRATheory(config);
                    theory = uflratheory;
                    thandler = new THandler(config, *uflratheory);
                    logic = &(theory->getLogic());
                    new_solver();
                    main_solver = new MainSolver(*thandler, config, solver, "qf_uflra solver");
                    main_solver->initialize();
            } else {
                notify_formatted(true, "unknown logic %s", logic_name);
            }
            break;
        }
        case t_setinfo:
        {
            if(parse_only)
            {
                break;
            }

            setInfo(**(n.children->begin()));
            break;
        }
        case t_getinfo:
        {
            if(parse_only)
            {
                break;
            }

            getInfo(**(n.children->begin()));
            break;
        }
        case t_setoption:
        {
            if(parse_only)
            {
                break;
            }

            setOption(**(n.children->begin()));
            break;
        }
        case  t_getoption:
        {
            if(parse_only)
            {
                break;
            }

            getOption(**(n.children->begin()));
            break;
        }
        case t_declaresort:
        {
            if (logic != NULL) {
                char* name = buildSortName(n);
                bool was_new = !logic->containsSort(name);
                free(name);
                SRef sr = newSort(n);
                if (!was_new) {
                    notify_formatted(true, "sort %s already declared", logic->getSortName(sr));
                }
                else {
                    notify_success();
                }
            }
            else
                notify_formatted(true, "illegal command before set-logic: declare-sort");
            break;
        }
        case t_declarefun:
        {
            if (logic != NULL) {
                if (declareFun(n))
                    notify_success();
            }
            else
                notify_formatted(true, "Illegal command before set-logic: declare-fun");
            break;
        }
        case t_declareconst:
        {
            if (logic != NULL) {
                declareConst(n);
            }
            else
                notify_formatted(true, "Illegal command before set-logic: declare-const");
            break;
        }
        case t_assert:
        {
            if (logic != NULL) {
                sstat status;
                ASTNode& asrt = **(n.children->begin());
                vec<LetFrame> let_branch;
                PTRef tr = parseTerm(asrt, let_branch);
                if (tr == PTRef_Undef)
                    notify_formatted(true, "assertion returns an unknown sort");
                else {
                    assertions.push(tr);
                    if (!parse_only)
                    {
                        char* err_msg = NULL;
                        status = main_solver->insertFormula(tr, &err_msg);

                        if (status == s_Error)
                            notify_formatted(true, "Error");
                        else if (status == s_Undef)
                            notify_success();
                        else if (status == s_False)
                            notify_success();

                        if (err_msg != NULL && status == s_Error)
                            notify_formatted(true, err_msg);
                        if (err_msg != NULL && status != s_Error)
                            comment_formatted(err_msg);
                        free(err_msg);
                    }
                }
            }
            else {
                notify_formatted(true, "Illegal command before set-logic: assert");
            }
            break;
        }
        case t_definefun:
        {
            if (logic != NULL) {
                defineFun(n);
            }
            else {
                notify_formatted(true, "Illegal command before set-logic: define-fun");
            }
            break;
        }
        case t_simplify:
        {
            if(parse_only)
                break;

            char* msg;
            int to;
            sstat status = main_solver->simplifyFormulas();
            if (status == s_Error)
                notify_formatted(true, "Simplify: %s", msg);
            break;
        }
        case t_checksat:
        {
            if(!parse_only)
                checkSat();
            break;
        }
        case t_getinterpolants:
        {
            if(!parse_only)
#ifdef PRODUCE_PROOF
                getInterpolants(n);
#else
                notify_formatted(true, "This binary has no support to interpolation");
#endif
            break;
        }
        case t_getassignment:
        {
            if(!parse_only)
                getAssignment();
            break;
        }
        case t_getvalue:
        {
            if(!parse_only)
                getValue(n.children);
            break;
        }
        case t_writestate:
        {
            if (parse_only) break;
            if (main_solver->solverEmpty()) {
                char* msg;
                int to;
                sstat status = main_solver->simplifyFormulas();
                if (status == s_Error)
                    notify_formatted(true, "write-state: %s", msg);
            }
            writeState((**(n.children->begin())).getValue());
            break;
        }
        case t_readstate:
        {
            if(parse_only) break;
            if (logic != NULL) {
                const char* filename = (**(n.children->begin())).getValue();
                CnfState cs;
                char* msg;
                bool rval = main_solver->readSolverState(filename, &msg);
                if (!rval) {
                    notify_formatted("%s", msg);
                }
            } else {
                notify_formatted(true, "Illegal command before set-logic: read-state");
            }
            break;
        }
        case t_writefuns:
        {
            const char* filename = (**(n.children->begin())).getValue();
            main_solver->writeFuns_smtlib2(filename);
            break;
        }
        case t_echo:
        {
            const char* str = (**(n.children->begin())).getValue();
            notify_formatted(false, "%s", str);
            break;
        }
        case t_push:
        {
            if(!parse_only)
                push();
            break;
        }
        case t_pop:
        {
            if(!parse_only)
                pop();
            break;
        }
        case t_exit:
        {
            if (parse_only) break;
            exit();
            notify_success();
            break;
        }
        default:
        {
            notify_formatted(true, "Unknown command encountered!");
        }
    }
}

// Adds a new term to TermTable and a mapping to the term from this let frame.
// returns true in success and false if
//   (i) the frame contains the term or
//  (ii) if an error occurred in inserting the term to the termtable for some reason, or
// (iii) if the name is non-redefinable in the logic.
// Overloading let variables is not supported at the moment
bool Interpret::addLetName(const char* s, const PTRef tr, LetFrame& frame) {
    if (frame.contains(s)) {
        comment_formatted("Overloading let variables makes no sense: %s", s);
        return false;
    }
    // If a term is noscoping with one name, all others are also
    // noscoping.
    if (logic->hasSym(s) && logic->getSym(logic->symNameToRef(s)[0]).noScoping()) {
        comment_formatted("Names marked as no scoping cannot be overloaded with let variables: %s", s);
        return false;
    }

    frame.insert(s, tr);
    return true;
}

//
// Determine whether the term refers to some let definition
//
PTRef Interpret::letNameResolve(const char* s, const vec<LetFrame>& let_branch) const {
    // We need to try the let branch we're in
    for (int i = let_branch.size()-1; i >= 0; i--) {
        if (let_branch[i].contains(s)) {
            PTRef tref = let_branch[i][s];
            return tref;
        }
    }
    return PTRef_Undef;
}

//
// Typecheck the term structure.  Construct the terms.
//
// TODO: left and right associativity, pairwisety - integrate these to the congruence algorithm,
//       chainability - not yet implemented
//       attributed terms - working now on this

PTRef Interpret::parseTerm(const ASTNode& term, vec<LetFrame>& let_branch) {
    ASTType t = term.getType();
    if (t == TERM_T) {
        const char* name = (**(term.children->begin())).getValue();
//        comment_formatted("Processing term %s", name);
        const char* msg;
        vec<SymRef> params;
        //PTRef tr = logic->resolveTerm(name, vec_ptr_empty, &msg);
        PTRef tr = logic->mkConst(name, &msg);
        if (tr == PTRef_Undef)
            comment_formatted("While processing %s: %s", name, msg);
        return tr;
    }

    else if (t == QID_T) {
        const char* name = (**(term.children->begin())).getValue();
//        comment_formatted("Processing term with symbol %s", name);
        PTRef tr = letNameResolve(name, let_branch);
        char* msg = NULL;
        if (tr != PTRef_Undef) {
//            comment_formatted("Found a let reference to term %d", tr);
            return tr;
        }
        tr = logic->resolveTerm(name, vec_ptr_empty, &msg);
        if (tr == PTRef_Undef)
            comment_formatted("unknown qid term %s: %s", name, msg);
        free(msg);
        return tr;
    }

    else if ( t == LQID_T ) {
        // Multi-argument term
        list<ASTNode*>::iterator node_iter = term.children->begin();
        vec<PTRef> args;
        const char* name = (**node_iter).getValue(); node_iter++;
        // Parse the arguments
        for (; node_iter != term.children->end(); node_iter++) {
            PTRef arg_term = parseTerm(**node_iter, let_branch);
            if (arg_term == PTRef_Undef)
                return PTRef_Undef;
            else
                args.push(arg_term);
        }
        assert(args.size() > 0);
        char* msg = NULL;
        PTRef tr = logic->resolveTerm(name, args, &msg);
        if (tr == PTRef_Undef) {
            notify_formatted(true, "No such symbol %s: %s", name, msg);
            comment_formatted("The symbol %s is not defined for the following sorts:", name);
            for (int j = 0; j < args.size(); j++)
                comment_formatted("arg %d: %s", j, logic->getSortName(logic->getSortRef(args[j]) )); //store.getName(symstore[ptstore[args[j]].symb()].rsort()));
            if (logic->hasSym(name)) {
                comment_formatted("candidates are:");
                const vec<SymRef>& trefs = logic->symNameToRef(name);
                for (int j = 0; j < trefs.size(); j++) {
                    SymRef ctr = trefs[j];
                    const Symbol& t = logic->getSym(ctr);
                    comment_formatted(" candidate %d", j);
                    for (uint32_t k = 0; k < t.nargs(); k++) {
                        comment_formatted("  arg %d: %s", k, logic->getSortName(t[k]));
                    }
                }
            }
            else
                comment_formatted("There are no candidates.");
            free(msg);
            return PTRef_Undef;
        }


        return tr;
    }

    else if (t == LET_T) {
        std::list<ASTNode*>::iterator ch = term.children->begin();
        std::list<ASTNode*>::iterator vbl = (**ch).children->begin();
        let_branch.push(); // The next scope, where my vars will be defined
        vec<PTRef> tmp_args;
        vec<char*> names;
        // First read the term declarations in the let statement
        while (vbl != (**ch).children->end()) {
            PTRef let_tr = parseTerm(**((**vbl).children->begin()), let_branch);
            if (let_tr == PTRef_Undef) return PTRef_Undef;
            tmp_args.push(let_tr);
            char* name = strdup((**vbl).getValue());
            names.push(name);
            vbl++;
        }
        // Only then insert them to the table
        for (int i = 0; i < tmp_args.size(); i++) {
//            vec<TRef> args;
//            args.push(tmp_args[i]);
            if (addLetName(names[i], tmp_args[i], let_branch[let_branch.size()-1]) == false) {
                comment_formatted("Let name addition failed");
                for (int i = 0; i < names.size(); i++) free(names[i]);
                return PTRef_Undef;
            }
            assert(let_branch[let_branch.size()-1].contains(names[i]));
        }
        ch++;
        // This is now constructed with the let declarations context in let_branch
        PTRef tr = parseTerm(**(ch), let_branch);
        if (tr == PTRef_Undef) {
            comment_formatted("Failed in parsing the let scoped term");
            for (int i = 0; i < names.size(); i++) free(names[i]);
            return PTRef_Undef;
        }
        let_branch.pop(); // Now the scope is unavailable for us
        for (int i = 0; i < names.size(); i++)
            free(names[i]);
        return tr;
    }

    else if (t == BANG_T) {
        assert(term.children->size() == 2);
        std::list<ASTNode*>::iterator ch = term.children->begin();
        ASTNode& named_term = **ch;
        ASTNode& attr_l = **(++ ch);
        assert(attr_l.getType() == GATTRL_T);
        assert(attr_l.children->size() == 1);
        ASTNode& name_attr = **(attr_l.children->begin());

        PTRef tr = parseTerm(named_term, let_branch);
        if (tr == PTRef_Undef) return tr;

        if (strcmp(name_attr.getValue(), ":named") == 0) {
            ASTNode& sym = **(name_attr.children->begin());
            assert(sym.getType() == SYM_T);
            const char* name = sym.getValue();
            if (nameToTerm.has(name)) {
                notify_formatted(true, "name %s already exists", name);
                return PTRef_Undef;
            }
            term_names.push(name);
            nameToTerm.insert(name, tr);
            if (!termToNames.has(tr)) {
                vec<const char*> v;
                termToNames.insert(tr, v);
            }
            termToNames[tr].push(name);
        }
        return tr;
    }
    else
        comment_formatted("Unknown term type");
    return PTRef_Undef;
}

bool Interpret::checkSat() {
    if (sat_calls > 0 && config.isIncremental() == false) {
            comment_formatted("Incrementality not enabled but %d check-sat encountered", sat_calls);
            return false;
    }
    sstat res;
    if (logic != nullptr) {
        sat_calls++;

        res = main_solver->check();

        if (res == s_True) {
            notify_formatted(false, "sat");
        }
        else if (res == s_False)
            notify_formatted(false, "unsat");
        else
            notify_formatted(false, "unknown");
    }
    else {
        notify_formatted(true, "Illegal command before set-logic: check-sat");
        return false;
    }
    if (res == s_Undef) {
        const SMTOption& o_dump_state = config.getOption(":dump-state");
        const SpType o_split = config.sat_split_type();
        char* name = config.dump_state();
        if (!o_dump_state.isEmpty() && o_split == spt_none)
            writeState(name);
        else if (o_split != spt_none) {
            if (config.smt_split_format() == spformat_smt2)
                writeSplits_smtlib2(name);
            else
                writeSplits(name);
        }
        free(name);
    }

    return true;
}

bool Interpret::push()
{
    if (config.isIncremental()) {
        main_solver->push();
        return true;
    }
    else {
        notify_formatted(true, "push encountered but solver not in incremental mode");
        return false;
    }
}

bool Interpret::pop()
{
    if (config.isIncremental()) {
        if (main_solver->pop())
            return true;
        else {
            notify_formatted(true, "Attempt to pop beyond the top of the stack");
            return false;
        }
    }
    else {
        notify_formatted(true, "pop encountered but solver not in incremental mode");
        return false;
    }
}

bool Interpret::getAssignment() {
    if (logic == NULL) {
       notify_formatted(true, "Illegal command before set-logic");
       return false;
    }
    if (main_solver->getStatus() != s_True) {
       notify_formatted(true, "Last solver call not satisfiable");
       return false;
    }
    std::stringstream ss;
    ss << '(';
    for (int i = 0; i < term_names.size(); i++) {
        const char* name = term_names[i];
        PTRef tr = nameToTerm[name];
        lbool val = main_solver->getTermValue(tr);
        ss << '(' << name << ' ' << (val == l_True ? "true" : (val == l_False ? "false" : "unknown"))
            << ')' << (i < term_names.size() - 1 ? " " : "");
    }
    ss << ')';
    const std::string& out = ss.str();
    notify_formatted(false, out.c_str());
    return true;
}

void Interpret::getValue(const list<ASTNode*>* terms)
{
    vec<ValPair> values;
    for (list<ASTNode*>::const_iterator term_it = terms->begin(); term_it != terms->end(); ++term_it) {
        const ASTNode& term = **term_it;
        vec<LetFrame> tmp;
        PTRef tr = parseTerm(term, tmp);
        if (tr != PTRef_Undef) {
            values.push(main_solver->getValue(tr));
            char* pt_str = logic->printTerm(tr);
            comment_formatted("Found the term %s", pt_str);
            free(pt_str);
        } else
            comment_formatted("Error parsing the term %s", (**(term.children->begin())).getValue());
    }
    printf("(");
    for (int i = 0; i < values.size(); i++) {
        char* name = logic->printTerm(values[i].tr);
        printf("(%s %s)", name, values[i].val);
        free(name);
    }
    printf(")\n");
}

void Interpret::writeState(const char* filename)
{
    char* msg;
    bool rval;

    if (config.smt_split_format() == spformat_osmt2)
        rval = main_solver->writeSolverState(filename, &msg);
    else if (config.smt_split_format() == spformat_smt2)
        rval = main_solver->writeSolverState_smtlib2(filename, &msg);

    if (!rval) {
        notify_formatted("%s", msg);
    }
}

void Interpret::writeSplits(const char* filename)
{
    char* msg;
    bool rval = main_solver->writeSolverSplits(filename, &msg);
    if (!rval) {
        notify_formatted("%s", msg);
    }
}

void Interpret::writeSplits_smtlib2(const char* filename)
{
    char* msg;
    main_solver->writeSolverSplits_smtlib2(filename, &msg);
}

bool Interpret::declareFun(ASTNode& n) // (const char* fname, const vec<SRef>& args)
{
    list<ASTNode*>::iterator it = n.children->begin();
    ASTNode& name_node = **(it++);
    ASTNode& args_node = **(it++);
    ASTNode& ret_node  = **(it++);
    assert(it == n.children->end());

    const char* fname = name_node.getValue();

    vec<SRef> args;

    char* name = buildSortName(ret_node);

    if (logic->containsSort(name)) {
        SRef sr = newSort(ret_node);
        args.push(sr);
        free(name);
    } else {
        notify_formatted(true, "Unknown return sort %s of %s", name, fname);
        free(name);
        return false;
    }
    for (list<ASTNode*>::iterator it2 = args_node.children->begin(); it2 != args_node.children->end(); it2++) {
        char* name = buildSortName(**it2);
        if (logic->containsSort(name)) {
            args.push(logic->getSortRef(name));
            free(name);
        }
        else {
            notify_formatted(true, "Undefined sort %s in function %s", name, fname);
            return false;
        }
    }
    char* msg;
    SRef rsort = args[0];
    vec<SRef> args2;

    for (int i = 1; i < args.size(); i++)
        args2.push(args[i]);

    SymRef rval = logic->declareFun(fname, rsort, args2, &msg);

    if (rval == SymRef_Undef) {
        comment_formatted("While declare-fun %s: %s", fname, msg);
        free(msg);
        return false;
    }
    return true;
}

bool Interpret::declareConst(ASTNode& n) //(const char* fname, const SRef ret_sort)
{
    list<ASTNode*>::iterator it = n.children->begin();
    ASTNode& name_node = **(it++);
    ASTNode& args_node = **(it++);
    ASTNode& ret_node = **(it++);
    const char* fname = name_node.getValue();
    char* name = buildSortName(ret_node);
    SRef ret_sort;
    if (logic->containsSort(name)) {
        ret_sort = newSort(ret_node);
    } else {
        notify_formatted(true, "Failed to declare constant %s", fname);
        notify_formatted(true, "Unknown return sort %s of %s", name, fname);
        free(name);
        return false;
    }

    PTRef rval = logic->mkConst(ret_sort, fname);
    if (rval == PTRef_Undef) {
        comment_formatted("While declare-const %s: %s", fname, "error");
        return false;
    }
    notify_success();
    return true;
}

bool Interpret::defineFun(const ASTNode& n)
{
    list<ASTNode*>::iterator it = n.children->begin();
    ASTNode& name_node = **(it++);
    ASTNode& args_node = **(it++);
    ASTNode& ret_node  = **(it++);
    ASTNode& term_node = **(it++);
    assert(it == n.children->end());

    const char* fname = name_node.getValue();

    // Get the argument sorts
    vec<SRef> arg_sorts;
    vec<PTRef> arg_trs;
    for (list<ASTNode*>::iterator it2 = args_node.children->begin(); it2 != args_node.children->end(); it2++) {
        string varName = (**it2).getValue();
        list<ASTNode*>::iterator varC = (**it2).children->begin();
        list<ASTNode*>::iterator varCC = (**varC).children->begin();
        string sortName = (**varCC).getValue();

        if (logic->containsSort(sortName.c_str())) {
            arg_sorts.push(logic->getSortRef(sortName.c_str()));
            //free(name);
            PTRef pvar = logic->mkVar(arg_sorts.last(), varName.c_str());
            arg_trs.push(pvar);
        }
        else {
            notify_formatted(true, "Undefined sort %s in function %s", sortName.c_str(), fname);
            return false;
        }
    }

    // The return sort
    char* rsort_name = buildSortName(ret_node);
    SRef ret_sort;
    if (logic->containsSort(rsort_name)) {
        ret_sort = newSort(ret_node);
        free(rsort_name);
    } else {
        notify_formatted(true, "Unknown return sort %s of %s", rsort_name, fname);
        free(rsort_name);
        return false;
    }

    sstat status;
    vec<LetFrame> let_branch;
    PTRef tr = parseTerm(term_node, let_branch);
    if (tr == PTRef_Undef) {
        notify_formatted(true, "define-fun returns an unknown sort");
        return false;
    }
    else if (logic->getSortRef(tr) != ret_sort) {
        notify_formatted(true, "define-fun term and return sort do not match: %s and %s\n", logic->getSortName(logic->getSortRef(tr)), logic->getSortName(ret_sort));
        return false;
    }
    bool rval = logic->defineFun(fname, arg_trs, ret_sort, tr);
    if (rval) notify_success();
    else {
        notify_formatted(true, "define-fun failed");
        return false;
    }

    return rval;
}


void Interpret::comment_formatted(const char* fmt_str, ...) const {
    va_list ap;
    int d;
    char c1, *t;
    if (config.verbosity() < 2) return;
    cout << "; ";

    va_start(ap, fmt_str);
    while (true) {
        c1 = *fmt_str++;
        if (c1 == '%') {
            switch (*fmt_str++) {
            case 's':
                t = va_arg(ap, char *);
                cout << t;
                break;
            case 'd':
                d = va_arg(ap, int);
                cout << d;
                break;
            case '%':
                cout << '%';
                break;
            }
        }
        else if (c1 != '\0')
            cout << c1;
        else break;
    }
    va_end(ap);
    cout << endl;
}


void Interpret::notify_formatted(bool error, const char* fmt_str, ...) {
    va_list ap;
    int d;
    char c1, *t;
    if (error)
        cout << "(error \"";

    va_start(ap, fmt_str);
    while (true) {
        c1 = *fmt_str++;
        if (c1 == '%') {
            switch (*fmt_str++) {
            case 's':
                t = va_arg(ap, char *);
                cout << t;
                break;
            case 'd':
                d = va_arg(ap, int);
                cout << d;
                break;
            case '%':
                cout << '%';
                break;
            }
        }
        else if (c1 != '\0')
            cout << c1;
        else break;
    }
    va_end(ap);
    if (error)
        cout << "\")" << endl;
//    else
//        cout << ")" << endl;
        cout << endl;
}

void Interpret::notify_success() {
    if (config.printSuccess())
        cout << "success" << endl;
}

void Interpret::execute(const ASTNode* r) {
    list<ASTNode*>::iterator i = r->children->begin();
    for (; i != r->children->end() && !f_exit; i++) {
        interp(**i);
    }
}

int Interpret::interpFile(FILE* in) {
    Smt2newContext context(in);
    int rval = smt2newparse(&context);

    if (rval != 0) return rval;

    const ASTNode* r = context.getRoot();
    execute(r);
    return rval;
}

int Interpret::interpFile(char *content){
    Smt2newContext context(content);
    int rval = smt2newparse(&context);

    if (rval != 0) return rval;

    const ASTNode* r = context.getRoot();
    execute(r);
    return rval;
}

/*
// For reading from pipe
int Interpret::interpPipe() {

    int buf_sz  = 16;
    char* buf   = (char*) malloc(sizeof(char)*buf_sz);
    int rd_head = 0;
    int rd_idx  = 0;

    bool done  = false;
    buf[0] = '\0';
    while (!done) {
        assert(buf[rd_head] == '\0');
        if (rd_head == buf_sz - 1) {
            buf_sz *= 2;
            buf = (char*) realloc(buf, sizeof(char)*buf_sz);
        }
        int rd_chunk = buf_sz - rd_head - 1;
        assert(rd_chunk > 0);
        int bts_rd = read(STDIN_FILENO, &buf[rd_head], rd_chunk);
        if (bts_rd == 0) {
            // Read EOF
            done = true;
            continue;
        }
        if (bts_rd < 0) {
            done = true;
            notify_formatted(true, sys_errlist[errno]);
            continue;
        }

        rd_head += bts_rd;
        int par     = 0;
        for (int i = 0; i < rd_head; i++) {
            char c = buf[i];
            if (c == '(') par ++;
            else if (c == ')') {
                par --;
                if (par == 0) {
                    // prepare parse buffer
                    char* buf_out = (char*) malloc(sizeof(char)*i+2);
                    // copy contents to the parse buffer
                    for (int j = 0; j <= i; j++)
                        buf_out[j] = buf[j];
                    buf_out[i+1] = '\0';
                    // copy remaining part buf
                    for (int j = i+1; j < rd_head; j++)
                        buf[j-i-1] = buf[j];
                    buf[rd_head-i-1] = '\0';
                    // update pointers
                    rd_head = rd_head-i-1;

                    Smt2newContext context(buf_out);
                    int rval = smt2newparse(&context);
                    if (rval != 0)
                        notify_formatted(true, "scanner");
                    else {
                        const ASTNode* r = context.getRoot();
                        execute(r);
                        done = f_exit;
                    }
                    free(buf_out);
                }
                if (par < 0) {
                    notify_formatted(true, "pipe reader: unbalanced parentheses");
                    done = true;
                }
            }
        }
    }
    free(buf);
    return 0;
}
*/

// For reading with readline.
int Interpret::interpInteractive(FILE*) {
    char *line_read = (char *) NULL;
    bool done = false;
    int rval = 0;
    int par = 0;
    int pb_cap = 1;
    int pb_sz = 0;
    char *parse_buf = (char *) malloc(pb_cap);

    while (!done) {
        if (line_read) {
            free(line_read);
            line_read = (char *) NULL;
        }

        if (par == 0)
            line_read = readline("> ");
        else if (par > 0)
            line_read = readline("... ");
        else {
            notify_formatted(true, "interactive reader: unbalanced parentheses");
            parse_buf[pb_sz-1] = 0; // replace newline with end of string
            add_history(parse_buf);
            pb_sz = 0;
            par = 0;
        }

        if (line_read && *line_read) {
            for (int i = 0; line_read[i] != '\0'; i++) {
                char c = line_read[i];
                if (c == '(') par ++;
                if (c == ')') par --;
                while (pb_cap - 2 < pb_sz) { // the next char and terminating zero
                    pb_cap *= 2;
                    parse_buf = (char*) realloc(parse_buf, pb_cap);
                }
                parse_buf[pb_sz ++] = c;
            }
            if (par == 0) {
                parse_buf[pb_sz] = '\0';
                // Parse starting from the command nonterminal
                // Parsing should be done from a string that I get from the readline
                // library.
                Smt2newContext context(parse_buf);
                int rval = smt2newparse(&context);
                if (rval != 0)
                    notify_formatted(true, "scanner");
                else {
                    const ASTNode* r = context.getRoot();
                    execute(r);
                    done = f_exit;
                }
                add_history(parse_buf);
                pb_sz = 0;
            }
            else { // add the line break
                while (pb_cap - 2 < pb_sz) { // the next char and terminating zero
                    pb_cap *= 2;
                    parse_buf = (char*) realloc(parse_buf, pb_cap);
                }
                parse_buf[pb_sz ++] = '\n';
            }
        }
    }
    if (parse_buf) free(parse_buf);
    if (line_read) free(line_read);
    return rval;
}

// The Traversal of the node is unnecessary and a result of a confusion
// Code can possibly be reused when define-sort is implemented
char* Interpret::buildSortName(ASTNode& sn)
{
    list<ASTNode*>::iterator it = sn.children->begin();
    char* canon_name;
    int written = asprintf(&canon_name, "%s", (**it).getValue());
    assert(written >= 0); (void)written;
    return canon_name;

//    MB: This code was not reachable, it seems to handle paramteric sorts, but that is not really supported now
//    asprintf(&canon_name, "%s", (**(it++)).getValue());
//    if  (it != sn.children->end()) {
//        char* arg_names;
//        char* old;
//        char* sub_name = buildSortName(**(it++));
//        asprintf(&arg_names, "%s", sub_name);
//        free(sub_name);
//        for (; it != sn.children->end(); it++) {
//            old = arg_names;
//            sub_name = buildSortName(**it);
//            asprintf(&arg_names, "%s %s", old, sub_name);
//            free(sub_name);
//            free(old);
//        }
//        old = canon_name;
//        asprintf(&canon_name, "%s (%s)", old, arg_names);
//        free(old);
//    }
//    return canon_name;
}

SRef Interpret::newSort(ASTNode& sn) {
//    IdRef idr = IdRef_Undef;
//    vec<SRef> tmp;
//    if (sn.getType() == CMD_T || sn.getType() == ID_T) {
//        list<ASTNode*>::iterator p = sn.children->begin();
//        ASTNode& sym_name = **p;
//        char* name = sym_name.getValue();
//        idr = logic->newIdentifier(sym_name.getValue());
//    } else {
//        assert(sn.getType() == LID_T);
//        // This is possibly broken: idr is undef once we exit here.
//        list<ASTNode*>::iterator it = sn.children->begin();
//        for (; it != sn.children->end(); it++)
//            tmp.push(newSort(**it));
//    }
//    char* canon_name = buildSortName(sn);
//    SRef rval = logic->newSort(idr, canon_name, tmp);
//    free(canon_name);

    char* msg;
    char* canon_name = buildSortName(sn);
    SRef rval = logic->declareSort(canon_name, &msg);
    return rval;
}

#ifdef PRODUCE_PROOF
void Interpret::getInterpolants(const ASTNode& n)
{
    auto exps = *n.children;
    vec<PTRef> grouping; // Consists of PTRefs that we want to group
    for (auto e : exps) {
        ASTNode& c = *e;
        vec<LetFrame> v;
        v.push_m(LetFrame(nameToTerm));
        PTRef tr = parseTerm(c, v);
//        printf("Itp'ing a term %s\n", logic->pp(tr));
        grouping.push(tr);
    }

    if (!(config.produce_inter() > 0))
        opensmt_error("Cannot interpolate");

    assert(grouping.size() >= 2);
    vec<ipartitions_t> partitionings;
    ipartitions_t p = 0;
    // We assume that together the groupings cover all query, so we ignore the last argument, since that should contain all that was missing at that point
    for (int i = 0; i < grouping.size() - 1; i++)
    {
        PTRef group = grouping[i];
        if (is_top_level_assertion(group))
        {
            int assertion_index = get_assertion_index(group);
            assert(assertion_index >= 0);
            opensmt::setbit(p, static_cast<unsigned int>(assertion_index));
        }
        else {
            assert(logic->isAnd(group));
            Pterm & and_t = logic->getPterm(group);
            for (int j = 0; j < and_t.size(); j++) {
                PTRef tr = and_t[j];
                assert(is_top_level_assertion(tr));
                int assertion_index = get_assertion_index(tr);
                assert(assertion_index >= 0);
                opensmt::setbit(p, static_cast<unsigned int>(assertion_index));
            }
        }
        partitionings.push_c(p);
    }
        SimpSMTSolver& smt_solver = main_solver->getSMTSolver();
        smt_solver.createProofGraph();
        if(config.proof_reduce())
            smt_solver.reduceProofGraph();
//        cerr << "Computing interpolant with mask " << p << endl;
        vec<PTRef> itps;
        if(partitionings.size() > 1){
            smt_solver.getPathInterpolants(itps, partitionings);
        }
        else{
            smt_solver.getSingleInterpolant(itps, partitionings[0]);
        }

        for (int j = 0; j < itps.size(); j++) {
            char* itp = logic->pp(itps[j]);
            notify_formatted(false, "%s", itp);
            free(itp);
        }
}
#endif

bool Interpret::is_top_level_assertion(PTRef ref) {
    return get_assertion_index(ref) >= 0;
}

int Interpret::get_assertion_index(PTRef ref) {
    for (int i = 0; i < assertions.size(); ++i) {
        if (ref == assertions[i]) { return i;}
    }
    return -1;
}



