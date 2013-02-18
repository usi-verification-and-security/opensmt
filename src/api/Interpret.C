#include <assert.h>
#include <stdarg.h>
#include <string.h>
#include <sstream>
#include <readline/readline.h>
#include <readline/history.h>
#include "Interpret.h"
#include "Term.h"

namespace opensmt {
bool stop;
};

uint32_t LetFrame::id_cnt = 0;

/*********************************************************************
 * Generic configuration class, used for both set-info and set-option
 *********************************************************************/

ConfValue::ConfValue(const ASTNode& s_expr_n) {
    if (s_expr_n.getType() == SEXPRL_T) {
        type = O_LIST;
        configs = new list<ConfValue*>;
        for (list<ASTNode*>::iterator i = s_expr_n.children->begin(); i != s_expr_n.children->end(); i++)
            configs->push_back(new ConfValue(**i));
    }
    else if (s_expr_n.getType() == SYM_T) {
        type   = O_SYM;
        strval = strdup(s_expr_n.getValue());
    }
    else if (s_expr_n.getType() == SPECC_T) {
        ASTNode& spn = **(s_expr_n.children->begin());
        if (spn.getType() == NUM_T) {
           type = O_NUM;
           numval = atoi(spn.getValue());
        }
        else if (spn.getType() == DEC_T) {
            type = O_DEC;
            char* end;
            decval = strtod(spn.getValue(), &end);
            assert(end != NULL);
        }
        else if (spn.getType() == HEX_T) {
            type = O_HEX;
            string tmp(spn.getValue());
            tmp.erase(0,2);
            char* end;
            unumval = strtoul(tmp.c_str(), &end, 16);
            assert(end != NULL);
        }
        else if (spn.getType() == BIN_T) {
            type = O_BIN;
            string tmp(spn.getValue());
            tmp.erase(0,2);
            char* end;
            unumval = strtoul(tmp.c_str(), &end, 2);
            assert(end != NULL);
        }
        else if (spn.getType() == STR_T) {
            type = O_STR;
            strval = strdup(spn.getValue());
        }
        else assert(false);
    }
    else if (s_expr_n.getType() == UATTR_T) {
        type = O_ATTR;
        strval = strdup(s_expr_n.getValue());
    }
    else assert(false); //Not implemented
}

char* ConfValue::toString() {
    if (type == O_BOOL)
        return numval == 1 ? strdup("true") : strdup("false");
    if (type == O_STR)
        return strdup(strval);
    if (type == O_NUM) {
        stringstream ss;
        ss << numval;
        return strdup(ss.str().c_str());
    }
    if (type == O_EMPTY) {
        return strdup("");
    }
    if (type == O_ATTR) {
        return strdup(strval);
    }
    if (type == O_DEC) {
        stringstream ss;
        ss << decval;
        return strdup(ss.str().c_str());
    }
    if (type == O_HEX) {
        stringstream ss;
        ss << unumval;
        return strdup(ss.str().c_str());
    }
    if (type == O_BIN) {
        stringstream ss;
        ss << unumval;
        return strdup(ss.str().c_str());
    }
    if (type == O_SYM) {
        return strdup(strval);
    }
    if (type == O_LIST) {
        stringstream ss;
        ss << "( ";
        for (list<ConfValue*>::iterator it = configs->begin(); it != configs->end(); it++) {
            ss << *((*it)->toString()); ss << " "; }
        ss << ")";
        return strdup(ss.str().c_str());
    }
    return strdup("not implemented");
}


/***********************************************************
 * Class defining the information, configured with set-info
 ***********************************************************/

Info::Info(ASTNode& n) {
    assert( n.getType() == UATTR_T || n.getType() == PATTR_T );
    if (n.children == NULL) {
        value.type = O_EMPTY;
        return;
    }
    else {
        // n is now attribute_value
        n = **(n.children->begin());

        if (n.getType() == SPECC_T) {
            value = ConfValue(n);
        }
        else if (n.getType() == SYM_T) {
            value.strval = strdup(n.getValue());
            value.type = O_STR;
            return;
        }
        else if (n.getType() == SEXPRL_T) {
            value = ConfValue(n);
        }
        else assert(false);
    }
}

/***********************************************************
 * Class defining the options, configured with set-config
 ***********************************************************/

Option::Option(ASTNode& n) {
    assert(n.children != NULL);

    n = **(n.children->begin());

    if (n.getType() == BOOL_T) {
        value.type   = O_BOOL;
        value.numval = strcmp(n.getValue(), "true") == 0 ? 1 : 0;
        return;
    }
    if (n.getType() == STR_T) {
        value.type   = O_STR;
        value.strval = strdup(n.getValue());
        return;
    }
    if (n.getType() == NUM_T) {
        value.type   = O_NUM;
        value.numval = atoi(n.getValue());
        return;
    }

    assert( n.getType() == UATTR_T || n.getType() == PATTR_T );
    // The option is an attribute

    if (n.children == NULL) {
        value.type = O_EMPTY;
        return;
    }
    else {
        // n is now attribute_value
        n = **(n.children->begin());

        if (n.getType() == SPECC_T) {
            value = ConfValue(n);
        }
        else if (n.getType() == SYM_T) {
            value.strval = strdup(n.getValue());
            value.type = O_STR;
            return;
        }
        else if (n.getType() == SEXPRL_T) {
            value = ConfValue(n);
            /*
            */
        }
        else assert(false);
    }
}



/***********************************************************
 * Class defining interpreter
 ***********************************************************/



void Interpret::setInfo(ASTNode& n) {
    assert(n.getType() == UATTR_T || n.getType() == PATTR_T);

    Info*  value = new Info();
    char* name = strdup(n.getValue());

    if (infoTable.peek(name, *value)) {
//        printf("Updating an existing info %s\n", n.getValue());
        delete value;
        infoTable.remove(name);
        value = new Info(n);
    }
    else
        value = new Info(n);

    infoTable.insert(name, *value);
}

void Interpret::getInfo(ASTNode& n) {
    assert(n.getType() == INFO_T);

    char* name;

    if (n.getValue() != NULL)
        name = strdup(n.getValue());
    else {
        assert(n.children != NULL);
        name = strdup((**(n.children->begin())).getValue());
    }

    Info value;

    if (!infoTable.peek(name, value))
        notify_formatted(true, "no value for info %s", name);
    else
        notify_formatted(false, "%s %s", name, value.toString());
}

void Interpret::setOption(ASTNode& n) {
    assert(n.getType() == OPTION_T);
    char* name  = NULL;
    Option* value = NULL;

    if (n.getValue() == NULL)  {
        // Attribute
        ASTNode& an = **(n.children->begin());
        assert(an.getType() == UATTR_T || an.getType() == PATTR_T);
        name = strdup(an.getValue());
    }
    else // Normal option
        name = strdup(n.getValue());

    if (optionTable.contains(name)) {
        printf("Updating an existing option %s\n", name);
        optionTable.remove(name);
    }
    value = new Option(n);

    optionTable.insert(name, *value);
}

void Interpret::getOption(ASTNode& n) {
    assert(n.getType() == UATTR_T || n.getType() == PATTR_T );

    assert(n.getValue() != NULL);
    char* name = strdup(n.getValue());
    Option value;

    if (!optionTable.peek(name, value))
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
            else if (tstore[ptstore[tr].symb()].rsort() == store["Bool 0"]) {
                // Framework for handling different logic related simplifications?
                // cnfization of the formula
                // Get the egraph data structure for instance from here
                // Terms need to be purified before cnfization?
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
                notify_formatted(true, "Top-level assertion sort must be Bool, got %s", store[tstore[ptstore[tr].symb()].rsort()]->getCanonName());
                return false;
            }
        }
        else {
            notify_formatted(true, "Illegal command before set-logic: %s", cmd);
            return false;
        }
    }
    if ((strcmp(cmd, "check-sat") == 0)) {
        checkSat(cmd);
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
    if (tstore.contains(s) && tstore[tstore.nameToRef(s)[0]].noScoping()) {
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
//       The string based scoping is too slow

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
            tr = ptstore.lookupTerm(name, vec_empty);
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
                comment_formatted("arg %d: %s", j, store[tstore[ptstore[args[j]].symb()].rsort()]->getCanonName());
            comment_formatted("candidates are:");
            const vec<TRef>& trefs = tstore.nameToRef(name);
            for (int j = 0; j < trefs.size(); j++) {
                TRef ctr = trefs[j];
                const Term& t = tstore[ctr];
                comment_formatted(" candidate %d", j);
                for (uint32_t k = 0; k < t.nargs(); k++) {
                    comment_formatted("  arg %d: %s", k, store[t[k]]->getCanonName());
                }
            }
            return PTRef_Undef;
        }

//        for (int i = 0; i < args.size(); i++) {
//            tstore.insertOcc(args[i], i, tr);
//        }

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
    comment_formatted("Unknown term type");
    return PTRef_Undef;
}

bool Interpret::checkSat(const char* cmd) {
    if (logic.isSet()) {
        solver.initialize();
        lbool res = solver.solve();
        if (res == l_True) {
            notify_formatted(false, "sat");
            vec<ValPair>* val = ts.getModel();
            // This cannot of course be the final solution, but it would be nice to able to check if everything works
            for (int i = 0; i < val->size(); i++) {
                PTRef t_ref = (*val)[i].getTerm();
                lbool sign = (*val)[i].getVal();
                Pterm& t = ptstore[t_ref];
                if (logic.isEquality(t.symb())) {
                    if (tstore[t.symb()][0] != logic.getSort_bool()) {
                        char* term_str = ptstore.printTerm(t_ref);
                        comment_formatted("Term is uf equality: %s%s", sign == l_True ? "" : "not ", term_str);
                        free(term_str);
                        if (sign != l_Undef) {
                            lbool stat = uf_solver.addEquality(t_ref, sign == l_True);
                            if (stat == l_False) {
                                comment_formatted("Unsatisfiable");
                            }
                        }
                    }
                }
                else {
                    PTRef up_eq = logic.addUP(t_ref);
                    if (up_eq != PTRef_Undef) {
                        char* term_str = ptstore.printTerm(t_ref);
                        comment_formatted("Term is uninterpreted predicate: %s%s", sign == l_True ? "" : "not ", term_str);
                        free(term_str);
                        // We need to make the new term, but only if it does not already exist
                        lbool stat = uf_solver.addEquality(up_eq, sign == l_True);
                        if (stat == l_False) {
                            comment_formatted("Unsatisfiable");
                        }
                    }
                }
            }
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

bool Interpret::declareFun(const char* fname, const vec<SRef>& args) {
    bool rval = tstore.newTerm(fname, args);
    if (rval == false)
        comment_formatted("function %s already defined", fname);
    return rval;
}

void Interpret::comment_formatted(const char* fmt_str, ...) const {
    va_list ap;
    int d;
    char c1, *t;
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
    else
        cout << "(";

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
    else
        cout << ")" << endl;
}

void Interpret::notify_success() {
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
