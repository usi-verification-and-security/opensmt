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

#include "Interpret.h"
#include "Theory.h"
#include "UFLRATheory.h"
#include "Global.h"
#include "smt2tokens.h"
#include "MainSolver.h"
#include "LogicFactory.h"

#ifdef ITP_DEBUG
#include "TreeOps.h"
#endif // ITP_DEBUG

namespace opensmt {
bool stop;
};

/***********************************************************
 * Class defining interpreter
 ***********************************************************/

Interpret::~Interpret() {
    for (int i = 0; i < term_names.size(); ++i) {
        free(term_names[i]);
    }
}

PTRef
Interpret::getParsedFormula()
{
    PTRef root = main_solver->getLogic().mkAnd(assertions);
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
        notify_formatted(true, "set-option failed for %s: %s", name, msg);
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

using opensmt::Logic_t;
using opensmt::getLogicFromString;

void Interpret::interp(ASTNode& n) {
    assert(n.getType() == CMD_T);
    const smt2token cmd = n.getToken();
    switch (cmd.x) {
        case t_setlogic:
        {
            ASTNode &logic_n = **(n.children->begin());
            const char* logic_name = logic_n.getValue();
            if (isInitialized()) {
                notify_formatted(true, "logic has already been set to %s", main_solver->getLogic().getName());
            } else {
                auto logic_type = getLogicFromString(logic_name);
                if (logic_type == Logic_t::UNDEF) {
                    notify_formatted(true, "unknown logic %s", logic_name);
                    break;
                }
                initializeLogic(logic_type);
                main_solver.reset(new MainSolver(*logic, config, std::string(logic_name) + " solver"));
                main_solver->initialize();
                notify_success();
                }
            break;
        }
        case t_setinfo:
        {
            setInfo(**(n.children->begin()));
            notify_success();
            break;
        }
        case t_getinfo:
        {
            getInfo(**(n.children->begin()));
            break;
        }
        case t_setoption:
        {
            setOption(**(n.children->begin()));
            notify_success();
            break;
        }
        case  t_getoption:
        {
            getOption(**(n.children->begin()));
            break;
        }
        case t_declaresort:
        {
            if (isInitialized()) {
                Logic& logic = main_solver->getLogic();
                char* name = buildSortName(n);
                bool was_new = !logic.containsSort(name);
                free(name);
                SRef sr = newSort(n);
                if (!was_new) {
                    notify_formatted(true, "sort %s already declared", logic.getSortName(sr));
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
            if (isInitialized()) {
                if (declareFun(n))
                    notify_success();
            }
            else
                notify_formatted(true, "Illegal command before set-logic: declare-fun");
            break;
        }
        case t_declareconst:
        {
            if (isInitialized()) {
                declareConst(n);
            }
            else
                notify_formatted(true, "Illegal command before set-logic: declare-const");
            break;
        }
        case t_assert:
        {
            if (isInitialized()) {
                sstat status;
                ASTNode& asrt = **(n.children->begin());
                LetRecords letRecords;
                PTRef tr = parseTerm(asrt, letRecords);
                if (tr == PTRef_Undef)
                    notify_formatted(true, "assertion returns an unknown sort");
                else {
                    assertions.push(tr);
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
            else {
                notify_formatted(true, "Illegal command before set-logic: assert");
            }
            break;
        }
        case t_definefun:
        {
            if (isInitialized()) {
                defineFun(n);
            }
            else {
                notify_formatted(true, "Illegal command before set-logic: define-fun");
            }
            break;
        }
        case t_simplify:
        {
            sstat status = main_solver->simplifyFormulas();
            if (status == s_Error)
                notify_formatted(true, "Simplify");
            break;
        }
        case t_checksat:
        {
            checkSat();
            break;
        }
        case t_getinterpolants:
        {
            if (config.produce_inter()) {
                getInterpolants(n);
            } else {
                notify_formatted(true,
                                 "Option to produce interpolants has not been set, skipping this command ...");
            }
            break;
        }
        case t_getassignment:
        {
           getAssignment();
           break;
        }
        case t_getvalue:
        {
            getValue(n.children);
            break;
        }
        case t_getmodel:
        {
            if (not isInitialized()) {
                notify_formatted(true, "Illegal command before set-logic: get-model");
            }
            else if (main_solver->getStatus() != s_True) {
                notify_formatted(true, "Command get-model called, but solver is not in SAT state");
            }
            else {
                getModel();
            }
            break;
        }

        case t_writestate:
        {
            if (main_solver->solverEmpty()) {
                sstat status = main_solver->simplifyFormulas();
                if (status == s_Error)
                    notify_formatted(true, "write-state");
            }
            writeState((**(n.children->begin())).getValue());
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
            push();
            notify_success();
            break;
        }
        case t_pop:
        {
            pop();
            notify_success();
            break;
        }
        case t_exit:
        {
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


bool Interpret::addLetFrame(const vec<char *> & names, vec<PTRef> const& args, LetRecords& letRecords) {
    assert(names.size() == args.size());
    if (names.size() > 1) {
        // check that they are pairwise distinct;
        std::unordered_set<const char*, StringHash, Equal<const char*>> namesAsSet(names.begin(), names.end());
        if (namesAsSet.size() != names.size()) {
            comment_formatted("Overloading let variables makes no sense");
            return false;
        }
    }
    for (std::size_t i = 0; i < names.size(); ++i) {
        const char* name = names[i];
        if (logic->hasSym(name) && logic->getSym(logic->symNameToRef(name)[0]).noScoping()) {
            comment_formatted("Names marked as no scoping cannot be overloaded with let variables: %s", name);
            return false;
        }
        letRecords.addBinding(name, args[i]);
    }
    return true;
}

//
// Determine whether the term refers to some let definition
//
PTRef Interpret::letNameResolve(const char* s, const LetRecords& letRecords) const {
    return letRecords.getOrUndef(s);
}


PTRef Interpret::parseTerm(const ASTNode& term, LetRecords& letRecords) {
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
        PTRef tr = letNameResolve(name, letRecords);
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
        auto node_iter = term.children->begin();
        vec<PTRef> args;
        const char* name = (**node_iter).getValue(); node_iter++;
        // Parse the arguments
        for (; node_iter != term.children->end(); node_iter++) {
            PTRef arg_term = parseTerm(**node_iter, letRecords);
            if (arg_term == PTRef_Undef)
                return PTRef_Undef;
            else
                args.push(arg_term);
        }
        assert(args.size() > 0);
        char* msg = NULL;
        PTRef tr = PTRef_Undef;
        try {
            tr = logic->resolveTerm(name, args, &msg);
        }
        catch (LADivisionByZeroException & ex) {
            notify_formatted(true, ex.what());
            return PTRef_Undef;
        }
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
        auto ch = term.children->begin();
        auto vbl = (**ch).children->begin();
        vec<PTRef> tmp_args;
        vec<char*> names;
        // use RAII idiom to guard the scope of new LetFrame (and ensure the cleaup of names)
        class Guard {
            LetRecords& rec;
            vec<char*>& names;
        public:
            Guard(LetRecords& rec, vec<char*>& names): rec{rec}, names{names} { rec.pushFrame(); }
            ~Guard() { rec.popFrame(); for (int i = 0; i < names.size(); i++) { free(names[i]); }}
        } scopeGuard(letRecords, names);
        // First read the term declarations in the let statement
        while (vbl != (**ch).children->end()) {
            PTRef let_tr = parseTerm(**((**vbl).children->begin()), letRecords);
            if (let_tr == PTRef_Undef) return PTRef_Undef;
            tmp_args.push(let_tr);
            char* name = strdup((**vbl).getValue());
            names.push(name);
            vbl++;
        }
        // Only then insert them to the table
        bool success = addLetFrame(names, tmp_args, letRecords);
        if (not success) {
            comment_formatted("Let name addition failed");
            return PTRef_Undef;
        }
        ch++;
        // This is now constructed with the let declarations context in let_branch
        PTRef tr = parseTerm(**(ch), letRecords);
        if (tr == PTRef_Undef) {
            comment_formatted("Failed in parsing the let scoped term");
            return PTRef_Undef;
        }
        return tr;
    }

    else if (t == BANG_T) {
        assert(term.children->size() == 2);
        auto ch = term.children->begin();
        ASTNode& named_term = **ch;
        ASTNode& attr_l = **(++ ch);
        assert(attr_l.getType() == GATTRL_T);
        assert(attr_l.children->size() == 1);
        ASTNode& name_attr = **(attr_l.children->begin());

        PTRef tr = parseTerm(named_term, letRecords);
        if (tr == PTRef_Undef) return tr;

        if (strcmp(name_attr.getValue(), ":named") == 0) {
            ASTNode& sym = **(name_attr.children->begin());
            assert(sym.getType() == SYM_T);
            if (nameToTerm.has(sym.getValue())) {
                notify_formatted(true, "name %s already exists", sym.getValue());
                return PTRef_Undef;
            }
            char* name = strdup(sym.getValue());
            // MB: term_names becomes the owner of the string and is responsible for deleting
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
    sstat res;
    if (isInitialized()) {
        res = main_solver->check();

        if (res == s_True) {
            notify_formatted(false, "sat");
        }
        else if (res == s_False)
            notify_formatted(false, "unsat");
        else
            notify_formatted(false, "unknown");

        const Info& status = config.getInfo(":status");
        if (!status.isEmpty()) {
            std::string statusString(std::move(status.toString()));
            if ((statusString.compare("sat") == 0) && (res == s_False)) {
                notify_formatted(false, "(error \"check status which says sat\")");

            }
            else if ((statusString.compare("unsat") == 0) && (res == s_True)) {
                notify_formatted(false, "(error \"check status which says unsat\")");
            }
        }
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
            writeSplits_smtlib2(name);
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
    if (not isInitialized()) {
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

void Interpret::getValue(const std::vector<ASTNode*>* terms)
{
    Logic& logic = main_solver->getLogic();
    vec<ValPair> values;
    for (auto term_it = terms->begin(); term_it != terms->end(); ++term_it) {
        const ASTNode& term = **term_it;
        LetRecords tmp;
        PTRef tr = parseTerm(term, tmp);
        if (tr != PTRef_Undef) {
            values.push(main_solver->getValue(tr));
            char* pt_str = logic.printTerm(tr);
            comment_formatted("Found the term %s", pt_str);
            free(pt_str);
        } else
            comment_formatted("Error parsing the term %s", (**(term.children->begin())).getValue());
    }
    printf("(");
    for (int i = 0; i < values.size(); i++) {
        char* name = logic.printTerm(values[i].tr);
        printf("(%s %s)", name, values[i].val);
        free(name);
    }
    printf(")\n");
}

void Interpret::getModel() {

    auto model = main_solver->getModel();
    std::stringstream ss;
    ss << "(model\n";
    for (int i = 0; i < user_declarations.size(); ++i) {
        SymRef symref = user_declarations[i];
        const Symbol & sym = logic->getSym(symref);
        if (sym.size() == 1) {
            // variable, just get its value
            const char* s = logic->getSymName(symref);
            SRef symSort = sym.rsort();
            PTRef term = logic->mkVar(symSort, s);
            PTRef val = model->evaluate(term);
            ss << "(define-fun " << s  << " () " << logic->getSortName(symSort) << ' ' << logic->printTerm(val) << ')' << '\n';
        }
        else {
            char* s = logic->printSym(symref);
            notify_formatted(true, "Non-constant encountered during a model query: %s. This is not supported yet, ignoring...",  s);
            free(s);
        };
    }
    ss << ')';
    std::cout << ss.str() << std::endl;
}

void Interpret::writeState(const char* filename)
{
    char* msg;
    bool rval;

    rval = main_solver->writeSolverState_smtlib2(filename, &msg);

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
    auto it = n.children->begin();
    ASTNode& name_node = **(it++);
    ASTNode& args_node = **(it++);
    ASTNode& ret_node  = **(it++);
    assert(it == n.children->end());

    const char* fname = name_node.getValue();

    vec<SRef> args;

    char* name = buildSortName(ret_node);
    Logic& logic = main_solver->getLogic();

    if (logic.containsSort(name)) {
        SRef sr = logic.getSortRef(name);
        args.push(sr);
        free(name);
    } else {
        notify_formatted(true, "Unknown return sort %s of %s", name, fname);
        free(name);
        return false;
    }
    for (auto it2 = args_node.children->begin(); it2 != args_node.children->end(); it2++) {
        char* name = buildSortName(**it2);
        if (logic.containsSort(name)) {
            args.push(logic.getSortRef(name));
            free(name);
        }
        else {
            notify_formatted(true, "Undefined sort %s in function %s", name, fname);
            free(name);
            return false;
        }
    }
    char* msg;
    SRef rsort = args[0];
    vec<SRef> args2;

    for (int i = 1; i < args.size(); i++)
        args2.push(args[i]);

    SymRef rval = logic.declareFun(fname, rsort, args2, &msg);

    if (rval == SymRef_Undef) {
        comment_formatted("While declare-fun %s: %s", fname, msg);
        free(msg);
        return false;
    }
    user_declarations.push(rval);
    return true;
}

bool Interpret::declareConst(ASTNode& n) //(const char* fname, const SRef ret_sort)
{
    auto it = n.children->begin();
    ASTNode& name_node = **(it++);
    it++; // args_node
    ASTNode& ret_node = **(it++);
    const char* fname = name_node.getValue();
    char* name = buildSortName(ret_node);
    Logic& logic = main_solver->getLogic();
    SRef ret_sort;
    if (logic.containsSort(name)) {
        ret_sort = logic.getSortRef(name);
        free(name);
    } else {
        notify_formatted(true, "Failed to declare constant %s", fname);
        notify_formatted(true, "Unknown return sort %s of %s", name, fname);
        free(name);
        return false;
    }
    PTRef rval = logic.mkConst(ret_sort, fname);
    if (rval == PTRef_Undef) {
        comment_formatted("While declare-const %s: %s", fname, "error");
        return false;
    }
    notify_success();
    return true;
}

bool Interpret::defineFun(const ASTNode& n)
{
    auto it = n.children->begin();
    ASTNode& name_node = **(it++);
    ASTNode& args_node = **(it++);
    ASTNode& ret_node  = **(it++);
    ASTNode& term_node = **(it++);
    assert(it == n.children->end());

    const char* fname = name_node.getValue();
    Logic& logic = main_solver->getLogic();

    // Get the argument sorts
    vec<SRef> arg_sorts;
    vec<PTRef> arg_trs;
    for (auto it2 = args_node.children->begin(); it2 != args_node.children->end(); it2++) {
        string varName = (**it2).getValue();
        auto varC = (**it2).children->begin();
        auto varCC = (**varC).children->begin();
        string sortName = (**varCC).getValue();

        if (logic.containsSort(sortName.c_str())) {
            arg_sorts.push(logic.getSortRef(sortName.c_str()));
            //free(name);
            PTRef pvar = logic.mkVar(arg_sorts.last(), varName.c_str());
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
    if (logic.containsSort(rsort_name)) {
        ret_sort = logic.getSortRef(rsort_name);
        free(rsort_name);
    } else {
        notify_formatted(true, "Unknown return sort %s of %s", rsort_name, fname);
        free(rsort_name);
        return false;
    }

    sstat status;
    LetRecords letRecords;
    PTRef tr = parseTerm(term_node, letRecords);
    if (tr == PTRef_Undef) {
        notify_formatted(true, "define-fun returns an unknown sort");
        return false;
    }
    else if (logic.getSortRef(tr) != ret_sort) {
        notify_formatted(true, "define-fun term and return sort do not match: %s and %s\n", logic.getSortName(logic.getSortRef(tr)), logic.getSortName(ret_sort));
        return false;
    }
    bool rval = logic.defineFun(fname, arg_trs, ret_sort, tr);
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
    if (config.printSuccess()) {
        std::cout << "success" << std::endl;
    }
}

void Interpret::execute(const ASTNode* r) {
    auto i = r->children->begin();
    for (; i != r->children->end() && !f_exit; i++) {
        interp(**i);
        delete *i;
        *i = nullptr;
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


// For reading from pipe
int Interpret::interpPipe() {

    int buf_sz  = 16;
    char* buf   = (char*) malloc(sizeof(char)*buf_sz);
    int rd_head = 0;

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

            // obtain the error string
            char const * err_str = strerror(errno);

            // format the error
            notify_formatted(true, err_str);
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

// The Traversal of the node is unnecessary and a result of a confusion
// Code can possibly be reused when define-sort is implemented
char* Interpret::buildSortName(ASTNode& sn)
{
    auto it = sn.children->begin();
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
    SRef rval = main_solver->getLogic().declareSort(canon_name, &msg);
    return rval;
}

void Interpret::getInterpolants(const ASTNode& n)
{
    auto exps = *n.children;
    vec<PTRef> grouping; // Consists of PTRefs that we want to group
    LetRecords letRecords;
    letRecords.pushFrame();
    auto namedTermsPtrs = nameToTerm.getKeysAndValsPtrs();
    for (auto* namedTermPair : namedTermsPtrs) {
        letRecords.addBinding(namedTermPair->key, namedTermPair->data);
    }
    for (auto e : exps) {
        ASTNode& c = *e;
        PTRef tr = parseTerm(c, letRecords);
//        printf("Itp'ing a term %s\n", logic->pp(tr));
        grouping.push(tr);
    }
    letRecords.popFrame();

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
            bool ok = group != PTRef_Undef && logic->isAnd(group);
            if (ok) {
                Pterm const & and_t = logic->getPterm(group);
                for (int j = 0; j < and_t.size(); j++) {
                    PTRef tr = and_t[j];
                    ok = is_top_level_assertion(tr);
                    if (!ok) { break; }
                    int assertion_index = get_assertion_index(tr);
                    assert(assertion_index >= 0);
                    opensmt::setbit(p, static_cast<unsigned int>(assertion_index));
                }
            }
            if (!ok) {
                // error in interpolation command
                notify_formatted(true, "Invalid arguments of get-interpolants command");
                return;
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
        smt_solver.deleteProofGraph();

        for (int j = 0; j < itps.size(); j++) {
            char* itp = logic->pp(itps[j]);
            notify_formatted(false, "%s", itp);
            free(itp);
        }
}

bool Interpret::is_top_level_assertion(PTRef ref) {
    return get_assertion_index(ref) >= 0;
}

int Interpret::get_assertion_index(PTRef ref) {
    for (int i = 0; i < assertions.size(); ++i) {
        if (ref == assertions[i]) { return i;}
    }
    return -1;
}

void Interpret::initializeLogic(opensmt::Logic_t logicType) {
    logic.reset(opensmt::LogicFactory::getInstance(logicType));
}



