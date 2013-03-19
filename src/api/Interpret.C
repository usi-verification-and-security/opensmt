#include <assert.h>
#include <stdarg.h>
#include <string.h>
#include <sstream>
#include <readline/readline.h>
#include <readline/history.h>
#include "Interpret.h"

namespace opensmt {
bool stop;
};

uint32_t LetFrame::id_cnt = 0;


/***********************************************************
 * Class defining interpreter
 ***********************************************************/



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
    else
        notify_formatted(false, "%s %s", name, value.toString());
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

    Option value(n);
    config.setOption(name, value);
}

void Interpret::getOption(ASTNode& n) {
    assert(n.getType() == UATTR_T || n.getType() == PATTR_T );

    assert(n.getValue() != NULL);
    char* name = strdup(n.getValue());
//    Option value;

    const Option& value = config.getOption(name);

    if (value.isEmpty())
        notify_formatted(true, "No value for attr %s", name);
    else
        notify_formatted(false, "%s",value.toString());

}

void Interpret::exit() {
    f_exit = true;
}

bool Interpret::interp(ASTNode& n) {
    bool rval;
    assert(n.getType() == CMD_T);
    const char* cmd = n.getValue();
    if (strcmp(cmd, "set-logic") == 0) {
        ASTNode &logic_n = **(n.children->begin());
        const char* logic_name = logic_n.getValue();
        if (logic.isSet()) {
            notify_formatted(true, "logic has already been set to %s", logic.getName().c_str());
        }
        else {
            if (!logic.setLogic(logic_name)) {
                notify_formatted(true, "unknown logic %s", logic_name);
                return false;
            }
        }
        return true;
    }
    if (strcmp(cmd, "set-info") == 0) {
        setInfo(**(n.children->begin()));
        return false;
    }
    if (strcmp(cmd, "get-info") == 0) {
        getInfo(**(n.children->begin()));
        return false;
    }
    if (strcmp(cmd, "set-option") == 0) {
        setOption(**(n.children->begin()));
        return false;
    }
    if (strcmp(cmd, "get-option") == 0) {
        getOption(**(n.children->begin()));
        return false;
    }
    if (strcmp(cmd, "declare-sort") == 0) {
        if (logic.isSet()) {
            Sort* s = new Sort(n);
            if (store.contains(s->getCanonName())) {
                notify_formatted(true, "sort %s already declared", s->getCanonName());
                delete s;
                goto declare_sort_err;
            }
            store.insertStore(s);
            rval = logic.declare_sort_hook(s);
            assert(rval);
            notify_success();
declare_sort_err: ;
        }
        else
            notify_formatted(true, "illegal command before set-logic: %s", cmd);
        return false;
    }
    if (strcmp(cmd, "declare-fun") == 0) {
        if (logic.isSet()) {
            list<ASTNode*>::iterator it = n.children->begin();
            ASTNode& name_node = **(it++);
            ASTNode& args_node = **(it++);
            ASTNode& ret_node  = **(it++);
            assert(it == n.children->end());

            const char* fname = name_node.getValue();

            vec<SRef> args;

            Sort* s = new Sort(ret_node);
            const char* name = s->getCanonName();
            if (store.contains(name))
                args.push(store[*s]);
            else {
                notify_formatted(true, "Unknown return sort %s of %s", name, fname);
                goto declare_fun_err;
            }
            for (list<ASTNode*>::iterator it2 = args_node.children->begin(); it2 != args_node.children->end(); it2++) {
                Sort* s = new Sort(**it2);
                if (store.contains(*s)) {
                    SRef sr = store[*s];
                    args.push(sr);
                    delete s;
                }
                else {
                    const char* name = s->getCanonName();
                    notify_formatted(true, "Undefined sort %s in function %s", name, fname);
                    delete s;
                    goto declare_fun_err;
                }
            }
            if (declareFun(fname, args)) notify_success();
declare_fun_err: ;
        }
        else
            notify_formatted(true, "illegal command before set-logic: %s", cmd);
        return false;
    }
    if (strcmp(cmd, "assert") == 0) {
        if (logic.isSet()) {
            ASTNode& asrt = **(n.children->begin());
            vec<LetFrame> let_branch;
            PTRef tr = parseTerm(asrt, let_branch);
            if (tr == PTRef_Undef)
                notify_formatted(true, "assertion returns an unknown sort");
            else if (symstore[ptstore[tr].symb()].rsort() == store["Bool 0"]) {
                // Framework for handling different logic related simplifications?
                // cnfization of the formula
                // Get the egraph data structure for instance from here
                // Terms need to be purified before cnfization?
//                solver.cancelUntil(0);
                lbool state = ts.cnfizeAndGiveToSolver(tr);
                if (state == l_Undef)
                    notify_success();
                if (state == l_False) {
                    notify_success();
                    comment_formatted("The formula is trivially unsatisfiable");
                }
                comment_formatted("Inserted assertion");
                return true;
            }
            else {
                notify_formatted(true, "Top-level assertion sort must be Bool, got %s", store[symstore[ptstore[tr].symb()].rsort()]->getCanonName());
                return false;
            }
        }
        else {
            notify_formatted(true, "Illegal command before set-logic: %s", cmd);
            return false;
        }
    }
    if (strcmp(cmd, "check-sat") == 0) {
        checkSat(cmd);
    }

    if (strcmp(cmd, "get-assignment") == 0) {
        getAssignment(cmd);
    }
    if (strcmp(cmd, "exit") == 0) {
        exit();
        notify_success();
        //
        return false;
    }
    return false;
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
    if (symstore.contains(s) && symstore[symstore.nameToRef(s)[0]].noScoping()) {
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
    }

    else if (t == QID_T) {
        const char* name = (**(term.children->begin())).getValue();
//        comment_formatted("Processing term with symbol %s", name);
        PTRef tr = letNameResolve(name, let_branch);
        if (tr != PTRef_Undef) {
//            comment_formatted("Found a let reference to term %d", tr);
            return tr;
        }
        else
            tr = ptstore.lookupTerm(name, vec_ptr_empty);
        if (tr == PTRef_Undef)
            comment_formatted("unknown qid term %s", name);
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

        PTRef tr = ptstore.lookupTerm(name, args);
        if (tr == PTRef_Undef) {
            // Implement a nice error reporting here
            notify_formatted(true, "No such symbol %s", name);
            comment_formatted("The symbol %s is not defined for the following sorts:", name);
            for (int j = 0; j < args.size(); j++)
                comment_formatted("arg %d: %s", j, store[symstore[ptstore[args[j]].symb()].rsort()]->getCanonName());
            comment_formatted("candidates are:");
            const vec<SymRef>& trefs = symstore.nameToRef(name);
            for (int j = 0; j < trefs.size(); j++) {
                SymRef ctr = trefs[j];
                const Symbol& t = symstore[ctr];
                comment_formatted(" candidate %d", j);
                for (uint32_t k = 0; k < t.nargs(); k++) {
                    comment_formatted("  arg %d: %s", k, store[t[k]]->getCanonName());
                }
            }
            return PTRef_Undef;
        }


        return tr;
    }

    else if (t == LET_T) {
        std::list<ASTNode*>::iterator ch = term.children->begin();
        std::list<ASTNode*>::iterator vbl = (**ch).children->begin();
        let_branch.push(); // The next scope, where my vars will be defined
        vec<PTRef> tmp_args;
        vec<const char*> names;
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
                return PTRef_Undef;
            }
            assert(let_branch[let_branch.size()-1].contains(names[i]));
        }
        ch++;
        // This is now constructed with the let declarations context in let_branch
        PTRef tr = parseTerm(**(ch), let_branch);
        if (tr == PTRef_Undef) {
            comment_formatted("Failed in parsing the let scoped term");
            return PTRef_Undef;
        }
        let_branch.pop(); // Now the scope is unavailable for us
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
        assert(name_attr.getType() == PATTR_T);
        assert(strcmp(name_attr.getValue(), ":named") == 0);
        ASTNode& sym = **(name_attr.children->begin());
        assert(sym.getType() == SYM_T);
        const char* name = sym.getValue();
        if (nameToTerm.contains(name)) {
            notify_formatted(true, "name %s already exists", name);
            return PTRef_Undef;
        }
        PTRef tr = parseTerm(named_term, let_branch);
        nameToTerm.insert(name, tr);
        if (!termToNames.contains(tr)) {
            vec<const char*> v;
            termToNames.insert(tr, v);
        }
        termToNames[tr].push(name);
        term_names.push(name);
        return tr;
    }
    else
        comment_formatted("Unknown term type");
    return PTRef_Undef;
}

bool Interpret::checkSat(const char* cmd) {
    if (sat_calls > 0 && config.isIncremental() == false) {
            comment_formatted("Incrementality not enabled but %d check-sat encountered", sat_calls);
            return false;
    }
    if (logic.isSet()) {
        sat_calls++;
        ts.initialize();
//        lbool res = ts.solve();
        lbool res = l_True;
        ts.crashTest(1000);
        if (res == l_True) {
            notify_formatted(false, "sat");
        }
        else if (res == l_False)
            notify_formatted(false, "unsat");
        else
            notify_formatted(false, "unknown");
    }
    else {
        notify_formatted(true, "Illegal command before set-logic: %s", cmd);
        return false;
    }
    return true;
}

bool Interpret::getAssignment(const char* cmd) {
    if (!logic.isSet()) {
       notify_formatted(true, "Illegal command before set-logic: %s", cmd);
       return false;
    }
    if (ts.getStatus() != l_True) {
       notify_formatted(true, "Last solver call not satisfiable");
       return false;
    }
    char* out_str;
    asprintf(&out_str, "(");
    for (int i = 0; i < term_names.size(); i++) {
        const char* name = term_names[i];
        PTRef tr = nameToTerm[name];
        lbool val = ts.getTermValue(tr);
        asprintf(&out_str, "%s(%s %s)%s",
                 out_str,
                 name,
                 val == l_True ? "true" : "false",
                 i < term_names.size() - 1 ? " " : "");
    }

    asprintf(&out_str, "%s)", out_str);
    notify_formatted(false, out_str);
    free(out_str);
    return true;
}

bool Interpret::declareFun(const char* fname, const vec<SRef>& args) {
    SymRef rval = symstore.newSymb(fname, args);
    if (rval == SymRef_Undef) {
        comment_formatted("function %s already defined", fname);
        return false;
    }
    return true;
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
//    else
//        cout << "(";

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
