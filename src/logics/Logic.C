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


#include "SStore.h"
#include "PtStore.h"
#include "Logic.h"
#include "TreeOps.h"
#include "Global.h"
#include "Deductions.h"
#include <queue>
#include <set>

#ifdef PRODUCE_PROOF
#include <sys/wait.h>
#include <fstream>
#include <sstream>
#endif


using namespace std;

/***********************************************************
 * Class defining logic
 ***********************************************************/

const char* Logic::e_argnum_mismatch = "incorrect number of arguments";
const char* Logic::e_bad_constant    = "incorrect constant for logic";
const char* Logic::tk_true     = "true";
const char* Logic::tk_false    = "false";
const char* Logic::tk_not      = "not";
const char* Logic::tk_equals   = "=";
const char* Logic::tk_implies  = "=>";
const char* Logic::tk_and      = "and";
const char* Logic::tk_or       = "or";
const char* Logic::tk_xor      = "xor";
const char* Logic::tk_distinct = "distinct";
const char* Logic::tk_ite      = "ite";

const char* Logic::s_sort_bool = "Bool";
const char* Logic::s_ite_prefix = ".oite";
const char* Logic::s_framev_prefix = ".frame";

// The constructor initiates the base logic (Boolean)
Logic::Logic(SMTConfig& c) :
      config(c)
    , sort_store(config, id_store)
    , term_store(sym_store, sort_store)
    , sym_TRUE(SymRef_Undef)
    , sym_FALSE(SymRef_Undef)
    , sym_AND(SymRef_Undef)
    , sym_OR(SymRef_Undef)
    , sym_XOR(SymRef_Undef)
    , sym_NOT(SymRef_Undef)
    , sym_EQ(SymRef_Undef)
    , sym_IMPLIES(SymRef_Undef)
    , sym_DISTINCT(SymRef_Undef)
    , sym_ITE(SymRef_Undef)
    , sort_BOOL(SRef_Undef)
    , term_TRUE(PTRef_Undef)
    , term_FALSE(PTRef_Undef)
    , subst_num(0)
{
    config.logic = QF_UF;
    logic_type = QF_UF;
    IdRef bool_id = id_store.newIdentifier("Bool");
    vec<SRef> tmp_srefs;
    sort_store.newSort(bool_id, tmp_srefs);
    sort_BOOL = sort_store["Bool"];

    SymRef tr;

    char* msg;
    term_TRUE = mkConst(getSort_bool(), tk_true);
    if (term_TRUE == PTRef_Undef) {
        printf("Error in constructing term %s: %s\n", tk_true, msg);
        assert(false);
    }
    sym_TRUE = sym_store.nameToRef(tk_true)[0];
    sym_store[sym_TRUE].setNoScoping();

    vec<PTRef> tmp;

    term_FALSE = mkConst(getSort_bool(), tk_false);
    if (term_FALSE  == PTRef_Undef) {
        printf("Error in constructing term %s: %s\n", tk_false, msg);
        assert(false);
    }
    sym_FALSE = sym_store.nameToRef(tk_false)[0];
    sym_store[sym_FALSE].setNoScoping();

    vec<SRef> params;
    params.push(sort_BOOL);

    if ((sym_NOT = declareFun(tk_not, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_not, msg);
        assert(false);
    }
    sym_store[sym_NOT].setNoScoping();

    params.push(sort_BOOL);

    if ((sym_EQ = declareFun(tk_equals, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_equals, msg);
        assert(false);
    }
    if (sym_store[sym_EQ].setChainable() == false) { assert(false); }
    sym_store[sym_EQ].setNoScoping();
    sym_store[sym_EQ].setCommutes();
    equalities.insert(sym_EQ, true);

    if ((sym_IMPLIES = declareFun(tk_implies, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_implies, msg);
        assert(false);
    }
    if (sym_store[sym_IMPLIES].setRightAssoc() == false) { assert(false); }
    sym_store[sym_IMPLIES].setNoScoping();

    if ((sym_AND = declareFun(tk_and, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_and, msg);
        assert(false);
    }
    if (sym_store[sym_AND].setLeftAssoc() == false) { assert(false); }
    sym_store[sym_AND].setNoScoping();
    sym_store[sym_AND].setCommutes();

    if ((sym_OR = declareFun(tk_or, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_or, msg);
        assert(false);
    }
    if (sym_store[sym_OR].setLeftAssoc() == false) { assert(false); }
    sym_store[sym_OR].setNoScoping();
    sym_store[sym_OR].setCommutes();

    if ((sym_XOR = declareFun(tk_xor, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_xor, msg);
        assert(false);
    }
    if (sym_store[sym_XOR].setLeftAssoc() == false) { assert(false); }
    sym_store[sym_XOR].setNoScoping();
    sym_store[sym_XOR].setCommutes();

    if ((sym_DISTINCT = declareFun(tk_distinct, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_distinct, msg);
        assert(false);
    }
    if (sym_store[sym_DISTINCT].setPairwise() == false) { assert(false); }
    sym_store[sym_DISTINCT].setNoScoping();
    sym_store[sym_DISTINCT].setCommutes();
    disequalities.insert(sym_DISTINCT, true);

    if ((sym_ITE = declareFun(tk_ite, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_ite, msg);
        assert(false);
    }
    if (sym_store[sym_ITE].setLeftAssoc() == false) { assert(false); }
    sym_store[sym_ITE].setNoScoping();

    ites.insert(sym_ITE, true);
}

Logic::~Logic()
{
    cerr << "; -------------------------\n";
    cerr << "; STATISTICS FOR LOGICS\n";
    cerr << "; -------------------------\n";
    cerr << "; Substitutions............: " << subst_num << endl;
}

const Logic_t
Logic::getLogic() const
{
    return QF_UF;
}

const char*
Logic::getName() const
{
    return getLogic().str;
}

// Escape the symbol name if it contains a prohibited character from the
// following list:
//  - #
char*
Logic::printSym(SymRef sr) const
{
    // Entry is 1 if the corresponding ascii character requires quoting
    const bool quotable[256] =
    {
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 1, 0, 1, 1, 0, 0, 0, 1, // <space>, ", #, $, '
      1, 1, 0, 0, 1, 0, 0, 0, 0, 0, // (, ), <,>
      0, 0, 0, 0, 0, 0, 0, 0, 1, 1, // :, ;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 1, 0, 1, 0, 0, 1, 0, 0, 0, // [, ], `
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 0, 1, 0, 0, 0, 0, // {, }
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    };
    const char* name = sym_store.getName(sr);
    char* name_escaped;
    bool escape = false;
    for (int i = 0; name[i] != '\0'; i++)
    {
        if (quotable[(int)name[i]])
        {
            escape = true;
            break;
        }
    }
    if (escape)
        asprintf(&name_escaped, "|%s|", name);
    else
        asprintf(&name_escaped, "%s", name);

    return name_escaped;
}

char*
Logic::printTerm_(PTRef tr, bool ext, bool safe)
{
    char* out;

    if(safe && this->isIteVar(tr)){
        Ite ite = top_level_ites[tr];
        char *str_i = printTerm_(ite.i, ext, safe);
        char *str_t = printTerm_(ite.t, ext, safe);
        char *str_e = printTerm_(ite.e, ext, safe);

        asprintf(&out, "(ite %s %s %s)", str_i, str_t, str_e);

        free(str_i); free(str_t); free(str_e);

        return out;
    }

    const Pterm& t = getPterm(tr);
    SymRef sr = t.symb();
    char* name_escaped = printSym(sr);

    if (t.size() == 0) {
        if (ext)
            asprintf(&out, "%s <%d>", name_escaped, tr.x);
        else
            asprintf(&out, "%s", name_escaped);
        free(name_escaped);
        return out;
    }

    // Here we know that t.size() > 0

    char* old;
    asprintf(&out, "(%s ", name_escaped);
    free(name_escaped);

    for (int i = 0; i < t.size(); i++) {
        old = out;
        asprintf(&out, "%s%s", old, printTerm_(t[i], ext, safe));
        ::free(old);
        if (i < t.size()-1) {
            old = out;
            asprintf(&out, "%s ", old);
            ::free(old);
        }
    }
    old = out;
    if (ext)
        asprintf(&out, "%s) <%d>", old, tr.x);
    else
        asprintf(&out, "%s)", old);
    ::free(old);
    return out;
}

bool Logic::isTheoryTerm(PTRef ptr) const {
    const Pterm& p = term_store[ptr];
    SymRef sr = p.symb();
    if (sr == sym_EQ) {
        assert(p.nargs() == 2);
            return false;
    }
    else return isTheorySymbol(sr);
}

bool Logic::isTheorySymbol(SymRef tr) const {
    // True and False are special cases, we count them as theory symbols
    if (tr == sym_TRUE || tr == sym_FALSE) return true;
    const Symbol& t = sym_store[tr];
    // Boolean var
    if (t.rsort() == sort_BOOL && t.nargs() == 0) return false;
    // Standard Boolean operators
    if (tr == sym_NOT)      return false;
    if (tr == sym_EQ)       return false;
    if (tr == sym_IMPLIES)  return false;
    if (tr == sym_AND)      return false;
    if (tr == sym_OR)       return false;
    if (tr == sym_XOR)      return false;
    if (tr == sym_ITE)      return false;
    if (tr == sym_DISTINCT) return false;
    return true;
}

// description: Add equality for each new sort
// precondition: sort has been declared
bool Logic::declare_sort_hook(SRef sr) {
    vec<SRef> params;

    params.push(sr);
    params.push(sr);

    // Equality

    SymRef tr;

    char* msg;
    tr = declareFun(tk_equals, sort_BOOL, params, &msg, true);
    if (tr == SymRef_Undef) { return false; }
    sym_store[tr].setNoScoping();
    sym_store[tr].setCommutes();
    sym_store[tr].setChainable();
    equalities.insert(tr, true);

    // distinct
    tr = declareFun(tk_distinct, sort_BOOL, params, &msg, true);
    if (tr == SymRef_Undef) { return false; }
    if (sym_store[tr].setPairwise() == false) return false;
    sym_store[tr].setNoScoping();
    sym_store[tr].setCommutes();
    disequalities.insert(tr, true);

    // ite
    params.clear();
    params.push(sort_BOOL);
    params.push(sr);
    params.push(sr);

    tr = declareFun(tk_ite, sr, params, &msg, true);
    if (tr == SymRef_Undef) { return false; }
    sym_store[tr].setNoScoping();
    ites.insert(tr, true);

    return true;
}

void Logic::simplifyDisequality(PtChild& ptc, bool simplify) {

    if (!simplify) return;

    Pterm& t = term_store[ptc.tr];
    PTRef p; int i, j;
    for (i = j = 0, p = PTRef_Undef; i < t.size(); i++)
        if (t[i] == p) {
            term_store.free(ptc.tr);
            term_store[ptc.parent][ptc.pos] = getTerm_false();
        }
}

bool Logic::simplifyEquality(PtChild& ptc, bool simplify) {
    assert(isEquality(ptc.tr));
    if (!simplify) return false;
    Pterm& t = term_store[ptc.tr];

    PTRef p; int i, j;
    for (i = j = 0, p = PTRef_Undef; i < t.size(); i++)
        if (t[i] != p)
            t[j++] = p = t[i];
    if (j == 1) {
        term_store.free(ptc.tr); // Lazy free
        if (ptc.parent == PTRef_Undef)
            return true;
        term_store[ptc.parent][ptc.pos] = getTerm_true();
        ptc.tr = getTerm_true();
    }
    else {// shrink the size!
        t.shrink(i-j);
#ifdef VERBOSE_EUF
        if (i-j != 0)
            cout << term_store.printTerm(ptc.tr) << endl;
#endif
    }
    termSort(t);
    return false;
}


void
Logic::visit(PTRef tr, Map<PTRef,PTRef,PTRefHash>& tr_map)
{
    Pterm& p = getPterm(tr);
    vec<PTRef> newargs;
    char *msg;
    for(int i = 0; i < p.size(); ++i) {
        PTRef tr = p[i];
        if(tr_map.has(tr))
            newargs.push(tr_map[tr]);
        else
            newargs.push(tr);
    }
    PTRef trp = insertTerm(p.symb(), newargs, &msg);
    if (trp != tr) {
        if (tr_map.has(tr))
            assert(tr_map[tr] == trp);
        else
            tr_map.insert(tr, trp);
    }
}


//
// XXX Comments? This method is currently under development
//
lbool Logic::simplifyTree(PTRef tr, PTRef& root_out)
{
    vec<pi> queue;
    Map<PTRef,bool,PTRefHash> processed;
    Map<PTRef,PTRef,PTRefHash> tr_map;
    queue.push(pi(tr));
    lbool last_val = l_Undef;
    while (queue.size() != 0) {
        // First find a node with all children processed.
        int i = queue.size()-1;
        if (processed.has(queue[i].x)) {
            queue.pop();
            continue;
        }
        bool unprocessed_children = false;
        if (queue[i].done == false) {
#ifdef SIMPLIFY_DEBUG
            cerr << "looking at term num " << queue[i].x.x << endl;
#endif
            Pterm& t = getPterm(queue[i].x);
            for (int j = 0; j < t.size(); j++) {
                PTRef cr = t[j];
                if (!processed.has(cr)) {
                    unprocessed_children = true;
                    queue.push(pi(cr));
#ifdef SIMPLIFY_DEBUG
                    cerr << "pushing child " << cr.x << endl;
#endif
                }
            }
            queue[i].done = true;
        }
        if (unprocessed_children) continue;
#ifdef SIMPLIFY_DEBUG
        cerr << "Found a node " << queue[i].x.x << endl;
        cerr << "Before simplification it looks like " << term_store.printTerm(queue[i].x) << endl;
#endif
        processed.insert(queue[i].x, true);
        visit(queue[i].x, tr_map);
#ifdef PRODUCE_PROOF
        PTRef qaux = queue[i].x;
        if(tr_map.has(qaux) && isAssertion(qaux))
        {
            PTRef trq = tr_map[qaux];
            if(trq != qaux)
            {
                setOriginalAssertion(trq, qaux);
                assertions_simp.push(trq);
            }
        }
#endif
    }
    if (tr_map.has(tr))
        root_out = tr_map[tr];
    else
        root_out = tr;
}

// The vec argument might be sorted!
PTRef Logic::resolveTerm(const char* s, vec<PTRef>& args, char** msg) {
    SymRef sref = term_store.lookupSymbol(s, args);
    if (sref == SymRef_Undef) {
        if (defined_functions.has(s))
            return defined_functions[s];
        else {
            asprintf(msg, "Unknown symbol `%s'", s);
            return PTRef_Undef;
        }
    }
    assert(sref != SymRef_Undef);
    PTRef rval;
    char** msg2 = NULL;
    rval = insertTerm(sref, args, msg2);
    if (rval == PTRef_Undef)
        printf("Error in resolveTerm\n");

    return rval;
}


PTRef
Logic::mkIte(vec<PTRef>& args)
{
    if (!hasSortBool(args[0])) return PTRef_Undef;
    assert(args.size() == 3);
    if(isTrue(args[0])) return args[1];
    if(isFalse(args[0])) return args[2];
    if(args[0] == args[1]) return args[1];

    SRef sr = getSortRef(args[1]);
    if(sr != getSortRef(args[2]))
    {
        cerr << "ITE with different return sorts" << endl;
        assert(0);
    }

    char* name;
    static unsigned ite_counter = 0;
    asprintf(&name, "%s%d", s_ite_prefix, ite_counter++);
    PTRef o_ite = mkVar(sr, name);
    free(name);

    vec<PTRef> eq_args;
    eq_args.push(o_ite);
    eq_args.push(args[1]);
    PTRef eq1 = mkEq(eq_args);
    vec<PTRef> impl_args;
    impl_args.push(args[0]);
    impl_args.push(eq1);
    PTRef if_term = mkImpl(impl_args);

    eq_args.clear();
    eq_args.push(o_ite);
    eq_args.push(args[2]);
    PTRef eq2 = mkEq(eq_args);
    impl_args.clear();
    impl_args.push(mkNot(args[0]));
    impl_args.push(eq2);
    PTRef else_term = mkImpl(impl_args);

    vec<PTRef> and_args;
    and_args.push(if_term);
    and_args.push(else_term);

    PTRef repr = mkAnd(and_args);
    assert (repr != PTRef_Undef && o_ite != PTRef_Undef);
    assert(!top_level_ites.has(o_ite));

    Ite ite = {
            .i=args[0],
            .t=args[1],
            .e=args[2],
            .repr=repr
    };

    top_level_ites.insert(o_ite, ite);

    return o_ite;
}

// Check if arguments contain trues or a false and return the simplified
// term
PTRef Logic::mkAnd(vec<PTRef>& args) {
    char** msg;
    PTRef tr = PTRef_Undef;

    for (int i = 0; i < args.size(); i++)
        if (!hasSortBool(args[i]))
            return PTRef_Undef;

    if(args.size() == 0)
        tr = getTerm_true();
    else {
        sort(args, LessThan_PTRef());
        int i, j;
        PTRef p = PTRef_Undef;
        for (i = 0, j = 0; i < args.size(); i++) {
            if (p == args[i]) {} // skip
            else
                args[j++] = p = args[i];
        }
        args.shrink(i-j);
        vec<PTRef> newargs;
        for(int i = 0; i < args.size(); ++i)
        {
            if(isFalse(args[i])) {
                tr = getTerm_false();
                break;
            }
            if(!isTrue(args[i]))
                newargs.push(args[i]);
        }
        if(tr == PTRef_Undef) {
            if(newargs.size() == 0)
                tr = getTerm_true();
            else if(newargs.size() == 1)
                tr = newargs[0];
            else
                tr = insertTermHash(getSym_and(), newargs);
        }
    }

    if (tr == PTRef_Undef) {
        printf("Error in mkAnd: %s", *msg);
        assert(false);
    }

    return tr;
}

PTRef Logic::mkOr(vec<PTRef>& args) {
    PTRef tr = PTRef_Undef;

    for (int i = 0; i < args.size(); i++)
        if (!hasSortBool(args[i]))
            return PTRef_Undef;

    if(args.size() == 0)
        tr = getTerm_false();
    else {
        // Remove duplicates
        vec<PtAsgn> tmp_args;
        for (int i = 0; i < args.size(); i++) {
            if (isNot(args[i]))
                tmp_args.push(PtAsgn(getPterm(args[i])[0], l_False));
            else
                tmp_args.push(PtAsgn(args[i], l_True));
        }
        sort(tmp_args, LessThan_PtAsgn());
//        sort(args, LessThan_PTRef());
        int i, j;
        PtAsgn p = PtAsgn_Undef;
        for (i = 0, j = 0; i < tmp_args.size(); i++) {
            if (isTrue(tmp_args[i].tr)) {
                assert(tmp_args[i].sgn == l_True);
                return getTerm_true();
            } else if (isFalse(tmp_args[i].tr)) {
                assert(tmp_args[i].sgn == l_True);
            } else if (p == tmp_args[i]) { // skip
            } else if (p.tr == tmp_args[i].tr && p.sgn != tmp_args[i].sgn) {
                return getTerm_true();
            } else
                tmp_args[j++] = p = tmp_args[i];
        }
        tmp_args.shrink(i-j);
        if(tmp_args.size() == 0)
            return getTerm_false();
        else if(tmp_args.size() == 1)
            return tmp_args[0].sgn == l_True ? tmp_args[0].tr : mkNot(tmp_args[0].tr);
        vec<PTRef> newargs;
        for (int i = 0; i < tmp_args.size(); i++)
            newargs.push(tmp_args[i].sgn == l_True? tmp_args[i].tr : mkNot(tmp_args[i].tr));
        tr = insertTermHash(getSym_or(), newargs);
    }

    if(tr == PTRef_Undef) {
        printf("Error in mkOr");
        assert(0);
    }

    return tr;
}

PTRef Logic::mkXor(vec<PTRef>& args) {
    PTRef tr = PTRef_Undef;

    for (int i = 0; i < args.size(); i++)
        if (!hasSortBool(args[i]))
            return PTRef_Undef;

    if (args.size() != 2)
        return PTRef_Undef;
    else if (args[0] == args[1])
        return getTerm_false();
    else if (args[0] == mkNot(args[1]))
        return getTerm_true();
    else if (args[0] == getTerm_true() || args[1] == getTerm_true())
        return (args[0] == getTerm_true() ? mkNot(args[1]) : mkNot(args[0]));
    else if (args[0] == getTerm_false() || args[1] == getTerm_false())
        return (args[0] == getTerm_false() ? args[1] : args[0]);

    vec<PTRef> newargs;
    args.copyTo(newargs);
    sort(newargs);
    tr = insertTermHash(getSym_xor(), newargs);

    if(tr == PTRef_Undef) {
        printf("Error in mkXor");
        assert(0);
    }

    return tr;
}


PTRef
Logic::mkImpl(PTRef _a, PTRef _b)
{
    vec<PTRef> args;
    args.push(_a);
    args.push(_b);
    return mkImpl(args);
}

PTRef Logic::mkImpl(vec<PTRef>& args) {

    for (int i = 0; i < args.size(); i++)
        if (!hasSortBool(args[i]))
            return PTRef_Undef;

        assert(args.size() == 2);
        PTRef tr = PTRef_Undef;
        if (isFalse(args[0]))
                tr = getTerm_true();
        else if(isTrue(args[1]))
                tr = getTerm_true();
        else if(isTrue(args[0]) && isFalse(args[1]))
                tr = getTerm_false();
        else
        {
            vec<PTRef> or_args;
            or_args.push(mkNot(args[0]));
            or_args.push(args[1]);
            tr = mkOr(or_args);
        }

        if (tr == PTRef_Undef) {
                printf("Error in mkImpl");
                assert(0);
        }

        return tr;
}

PTRef Logic::mkEq(vec<PTRef>& args) {
    assert(args.size() == 2);
    if(isConstant(args[0]) && isConstant(args[1]))
        return (args[0] == args[1]) ? getTerm_true() : getTerm_false();
    if (args[0] == args[1]) return getTerm_true();
    SymRef eq_sym = term_store.lookupSymbol(tk_equals, args);
    // Simplify more here now that the equals type is known
    if (hasSortBool(eq_sym)) {
        if (args[0] == mkNot(args[1])) return getTerm_false();
        if (args[0] == getTerm_true() || args[1] == getTerm_true())
            return args[0] == getTerm_true() ? args[1] : args[0];
        if (args[0] == getTerm_false() || args[1] == getTerm_false())
            return args[0] == getTerm_false() ? mkNot(args[1]) : mkNot(args[0]);
    }
    return insertTermHash(eq_sym, args);
}

PTRef Logic::mkNot(vec<PTRef>& args) {
    assert(args.size() == 1);
    return mkNot(args[0]);
}

PTRef Logic::mkNot(PTRef arg) {
    PTRef tr = PTRef_Undef;
    if (!hasSortBool(arg)) return PTRef_Undef;
    if (isNot(arg))
        tr = getPterm(arg)[0];
    else if (isTrue(arg)) return getTerm_false();
    else if (isFalse(arg)) return getTerm_true();
    else {
        vec<PTRef> tmp;
        tmp.push(arg);
        tr = insertTermHash(getSym_not(), tmp);
    }

    if(tr == PTRef_Undef) {
        printf("Error in mkNot");
        assert(0);
    }

    return tr;
}

PTRef Logic::mkConst(const char* name, const char** msg)
{
    assert(0);
    return PTRef_Undef;
}


PTRef Logic::mkVar(SRef s, const char* name) {
    vec<SRef> sort_args;
    sort_args.push(s);
    char* msg;
    SymRef sr = newSymb(name, sort_args, &msg);
    if (sr == SymRef_Undef) {
        cerr << "Warning: while mkVar " << name << ": " << msg << endl;
        free(msg);
        assert(symNameToRef(name).size() == 1);
        sr = symNameToRef(name)[0];
    }
    vec<PTRef> tmp;
    PTRef ptr = insertTerm(sr, tmp, &msg);
    assert (ptr != PTRef_Undef);

    return ptr;
}

PTRef Logic::mkConst(SRef s, const char* name) {
    PTRef ptr = PTRef_Undef;
    if (s == sort_BOOL) {
        if ((strcmp(name, tk_true) != 0) && (strcmp(name, tk_false) != 0)) {
            char *msg = (char*)malloc(sizeof(e_bad_constant)+1);
            strcpy(msg, e_bad_constant);
            ptr = PTRef_Undef;
        }
        ptr = mkVar(s, name);
    } else {
        ptr = mkVar(s, name);
    }
    // Code to allow efficient constant detection.
//    int id = getPterm(ptr).getId();
    int id = sym_store[getPterm(ptr).symb()].getId();
    while (id >= constants.size())
        constants.push(false);
    constants[id] = true;

    return ptr;
}


PTRef Logic::mkFun(SymRef f, const vec<PTRef>& args, char** msg)
{
    PTRef tr;
    if (f == SymRef_Undef)
        tr = PTRef_Undef;
    else
        tr = Logic::insertTermHash(f, args);
    return tr;
}

PTRef Logic::mkBoolVar(const char* name)
{
    vec<SRef> tmp;
    char* msg;
    SymRef sr = declareFun(name, sort_BOOL, tmp, &msg);
    assert(sr != SymRef_Undef);
    vec<PTRef> tmp2;
    PTRef tr = mkFun(sr, tmp2, &msg);
    return tr;
}

// A term is literal if its sort is Bool and
//  (i)   number of arguments is 0
//  (ii)  its symbol is sym_NOT and argument is a literal (nested nots
//        create literals?)
//  (iii) it is an atom stating an equivalence of non-boolean terms (terms must be purified at this point)
bool Logic::isLit(PTRef tr) const
{
    const Pterm& t = getPterm(tr);
    if (sym_store[t.symb()].rsort() == getSort_bool()) {
        if (t.size() == 0) return true;
        if (t.symb() == getSym_not() ) return isLit(t[0]);
        // At this point all arguments of equivalence have the same sort.  Check only the first
        if (isEquality(tr) && (sym_store[getPterm(t[0]).symb()].rsort() != getSort_bool())) return true;
        if (isDisequality(tr) && !isDistinct(tr)) return true;
        if (isUP(tr)) return true;
    }
    return false;
}

SRef Logic::declareSort(const char* id, char** msg)
{
    IdRef idr = id_store.newIdentifier(id);
    vec<SRef> tmp;
    SRef sr = sort_store.newSort(idr, tmp);
    declare_sort_hook(sr);
    char* sort_name;
    asprintf(&sort_name, "%s", id);
    SRef rval = sort_store[sort_name];
    free(sort_name);
    return rval;
}

SymRef Logic::declareFun(const char* fname, const SRef rsort, const vec<SRef>& args, char** msg, bool interpreted)
{
    vec<SRef> comb_args;

    assert(rsort != SRef_Undef);

    comb_args.push(rsort);

    for (int i = 0; i < args.size(); i++) {
        assert(args[i] != SRef_Undef);
        comb_args.push(args[i]);
    }
    SymRef sr = sym_store.newSymb(fname, comb_args, msg);
    SymId id = getSym(sr).getId();
    for (int i = interpreted_functions.size(); i <= id; i++)
        interpreted_functions.push(false);
    interpreted_functions[id] = interpreted;
    return sr;
}

bool Logic::defineFun(const char* fname, const PTRef tr)
{
    if (defined_functions.has(fname))
        return false; // already there
    defined_functions.insert(fname, tr);
    return true;
}

PTRef Logic::insertTerm(SymRef sym, vec<PTRef>& terms, char** msg)
{
    if(sym == getSym_and())
        return mkAnd(terms);
    if(sym == getSym_or())
        return mkOr(terms);
    if(sym == getSym_xor())
        return mkXor(terms);
    if(sym == getSym_not())
        return mkNot(terms[0]);
    if(isEquality(sym))
        return mkEq(terms);
    if(sym == getSym_ite())
        return mkIte(terms);
    if(sym == getSym_implies())
        return mkImpl(terms);
    if(sym == getSym_true())
        return getTerm_true();
    if(sym == getSym_false())
        return getTerm_false();
    return insertTermHash(sym, terms);
}

bool
Logic::existsTermHash(SymRef sym, const vec<PTRef>& terms_in)
{
    vec<PTRef> terms;
    terms_in.copyTo(terms);
    PTRef res = PTRef_Undef;
    char **msg;
    if (terms.size() == 0) {
        if (term_store.hasCtermKey(sym)) //cterm_map.contains(sym))
            return true;
    }
    else if (!isBooleanOperator(sym)) {
        if (sym_store[sym].commutes()) {
            sort(terms, LessThan_PTRef());
        }
        PTLKey k;
        k.sym = sym;
        terms.copyTo(k.args);
        if (term_store.hasCplxKey(k))
            return true;
    }
    else {
        // Boolean operator
        PTLKey k;
        k.sym = sym;
        terms.copyTo(k.args);
        if (term_store.hasBoolKey(k))
            return true;
    }
    return false;
}

PTRef
Logic::insertTermHash(SymRef sym, const vec<PTRef>& terms_in)
{
    vec<PTRef> terms;
    terms_in.copyTo(terms);
    PTRef res = PTRef_Undef;
    char **msg;
    if (terms.size() == 0) {
        if (term_store.hasCtermKey(sym)) //cterm_map.contains(sym))
            res = term_store.getFromCtermMap(sym); //cterm_map[sym];
        else {
            res = term_store.newTerm(sym, terms);
            term_store.addToCtermMap(sym, res); //cterm_map.insert(sym, res);
        }
    }
    else if (!isBooleanOperator(sym)) {
        if (sym_store[sym].commutes()) {
            sort(terms, LessThan_PTRef());
        }
        if (!sym_store[sym].left_assoc() &&
            !sym_store[sym].right_assoc() &&
            !sym_store[sym].chainable() &&
            !sym_store[sym].pairwise() &&
            sym_store[sym].nargs() != terms.size_())
        {
            *msg = (char*)malloc(strlen(e_argnum_mismatch)+1);
            strcpy(*msg, e_argnum_mismatch);
            return PTRef_Undef;
        }
        PTLKey k;
        k.sym = sym;
        terms.copyTo(k.args);
        if (term_store.hasCplxKey(k))
            res = term_store.getFromCplxMap(k);
        else {
            res = term_store.newTerm(sym, terms);
            term_store.addToCplxMap(k, res);
        }
    }
    else {
        // Boolean operator
        PTLKey k;
        k.sym = sym;
        terms.copyTo(k.args);
        if (term_store.hasBoolKey(k)) {//bool_map.contains(k)) {
            res = term_store.getFromBoolMap(k); //bool_map[k];
#ifdef SIMPLIFY_DEBUG
            char* ts = printTerm(res);
            cerr << "duplicate: " << ts << endl;
            ::free(ts);
#endif
        }
        else {
            res = term_store.newTerm(sym, terms);
            term_store.addToBoolMap(k, res); //bool_map.insert(k, res);
#ifdef SIMPLIFY_DEBUG
            char* ts = printTerm(res);
            cerr << "new: " << ts << endl;
            ::free(ts);
#endif
        }
    }
    return res;
}

bool
Logic::isUF(SymRef sref) const
{
    return getSym(sref).nargs() > 0 && !interpreted_functions[getSym(sref).getId()];
}

bool Logic::isUF(PTRef ptr) const {
    return isUF(getSymRef(ptr)); //return (getPterm(ptr).size() > 0) && !interpreted_functions[getSym(ptr).getId()];
}

// Uninterpreted predicate p : U U* -> Bool
bool Logic::isUP(PTRef ptr) const {
    const Pterm& t = term_store[ptr];
    SymRef sr = t.symb();
    // Should this really be an uninterpreted predicate?
    // At least it falsely identifies (= true false) as an uninterpreted
    // predicate without the extra condition
    if (isEquality(sr) || isDisequality(sr)) {
        return false;
    }
    const Symbol& sym = sym_store[sr];
    if (sym.nargs() == 0) return false;
    if (sym.rsort() != getSort_bool()) return false;
    if (isBooleanOperator(sr)) return false;
    return true;
}

// Adds the uninterpreted predicate if ptr is an uninterpreted predicate.
// Returns reference to corresponding equality term or PTRef_Undef.  Creates
// the eq term if it does not exist.
// If the term is an equality (disequality), it must be an equality
// (disequality) over terms with non-boolean return type.  Those must be then
// returned as is.
PTRef Logic::lookupUPEq(PTRef ptr) {
    assert(isUP(ptr));
    // already seen
//    if (UP_map.contains(ptr)) return UP_map[ptr];
    // already an equality
    Pterm& t = term_store[ptr];
    if (isEquality(t.symb()) | isDisequality(t.symb()))
        return ptr;

    // Create a new equality
//    Symbol& sym = sym_store[t.symb()];
    vec<PTRef> args;
    args.push(ptr);
    args.push(getTerm_true());
    return mkEq(args);
//    return resolveTerm(tk_equals, args);
}

// Check if the term store contains an equality over the given arguments
// Return the reference if yes, return PTRef_Undef if no
// Changes the argument!
PTRef Logic::hasEquality(vec<PTRef>& args)
{
    SymRef sref = term_store.lookupSymbol(tk_equals, args);
    assert(sref != SymRef_Undef);
    sort(args, LessThan_PTRef());
    PTLKey k;
    k.sym = sref;
    args.copyTo(k.args);
    if (term_store.hasCplxKey(k))
        return term_store.getFromCplxMap(k);
    else
        return PTRef_Undef;
}

bool Logic::isBooleanOperator(SymRef tr) const {
    if (tr == getSym_and())     return true;
    if (tr == getSym_or())      return true;
    if (tr == getSym_not())     return true;
    if (tr == getSym_eq())      return true;
    if (tr == getSym_xor())     return true;
    if (tr == getSym_ite())     return true;
    if (tr == getSym_implies()) return true;
    if (tr == getSym_distinct()) return true;
    return false;
}

bool Logic::isConstant(SymRef sr) const
{
    int id = sym_store[sr].getId();
    if (constants.size() <= id) return false;
    return constants[id];
}

bool Logic::isAtom(PTRef r) const {
    const Pterm& t = term_store[r];
    if (sym_store[t.symb()].rsort() == getSort_bool()) {
        if (t.size() == 0) return true;
        if (t.symb() == getSym_not() ) return false;
        // At this point all arguments of equivalence have the same sort.  Check only the first
        if (isEquality(t.symb()) && (sym_store[term_store[t[0]].symb()].rsort() != getSort_bool())) return true;
        if (isUP(r)) return true;
        if (isDisequality(r)) return true;
    }
    return false;
}

//
// Compute the generalized substitution based on substs, and return in
// tr_new the corresponding term dag.
// Preconditions:
//  - all substitutions in substs must be on variables
//
bool Logic::varsubstitute(PTRef& root, Map<PTRef,PtAsgn,PTRefHash>& substs, PTRef& tr_new)
{
    Map<PTRef,PTRef,PTRefHash> gen_sub;
    vec<PTRef> queue;
    int n_substs = 0;

    queue.push(root);
    while (queue.size() != 0) {
        PTRef tr = queue.last();
#ifdef SIMPLIFY_DEBUG
        cerr << "processing " << printTerm(tr) << endl;
#endif
        if (gen_sub.has(tr)) {
            // Already processed
            queue.pop();
            continue;
        }
        bool unprocessed_children = false;
        Pterm& t = getPterm(tr);
        for (int i = 0; i < t.size(); i++) {
            if (!gen_sub.has(t[i])) {
                queue.push(t[i]);
                unprocessed_children = true;
            }
        }
        if (unprocessed_children) continue;
        queue.pop();
        PTRef result = PTRef_Undef;
        if (isVar(tr) || isConstant(tr)) {
            // The base case
            if (substs.has(tr) && substs[tr].sgn == l_True)
                result = substs[tr].tr;
            else
                result = tr;
            assert(!isConstant(tr) || result == tr);
            assert(result != PTRef_Undef);
        } else {
            // The "inductive" case
            if (substs.has(tr) && substs[tr].sgn == l_True) {
#ifdef SIMPLIFY_DEBUG
                printf("Immediate substitution found: %s -> %s\n", printTerm(tr), printTerm(substs[tr].tr));
#endif
                result = substs[tr].tr;
            }
            else {
                vec<PTRef> args_mapped;
#ifdef SIMPLIFY_DEBUG
                printf("Arg substitution found for %s:\n", printTerm(tr));
#endif
                for (int i = 0; i < t.size(); i++) {
                    args_mapped.push(gen_sub[t[i]]);
#ifdef SIMPLIFY_DEBUG
                    printf("  %s -> %s\n", printTerm(t[i]), printTerm(gen_sub[t[i]]));
#endif
                }
                char* msg;
                result = insertTerm(t.symb(), args_mapped, &msg);
#ifdef SIMPLIFY_DEBUG
                printf("  -> %s\n", printTerm(result));
#endif
            }
            assert(result != PTRef_Undef);
        }
        assert(result != PTRef_Undef);
        gen_sub.insert(tr, result);

        if (result != tr) {
            n_substs++;
#ifdef SIMPLIFY_DEBUG
            cerr << "Will substitute " << printTerm(tr) << " with " << printTerm(result) << endl;
#endif
        }
    }
    tr_new = gen_sub[root];
    return n_substs > 0;
}

//
// Identify and break any substitution loops
//
void Logic::breakSubstLoops(Map<PTRef,PtAsgn,PTRefHash>& substs)
{
    int iters;
    vec<SubstNode*> alloced;
    for (iters = 0; ; iters++) {
        if (substs.getSize() == 0) return;

        const char white = 0;
        const char black = 2;
        const char undef = 3;

        vec<PTRef> keys;
        Map<PTRef,SubstNode*,PTRefHash> varToSubstNode;
        substs.getKeys(keys);
        vec<char> seen;
        // Color all variables that appear as keys white
        for (int i = 0; i < keys.size(); i++) {
            int id = getPterm(keys[i]).getId();
            while (id >= seen.size())
                seen.push(undef);
            seen[id] = white;
        }
        vec<SubstNode*> roots;
        for (int i = 0; i < keys.size(); i++) {
            int id = getPterm(keys[i]).getId();
            vec<SubstNode*> queue;
            if (seen[id] == white && substs[keys[i]].sgn == l_True) {
                SubstNode* n = new SubstNode(keys[i], substs[keys[i]].tr, NULL, *this);
                alloced.push(n);
                queue.push(n);
                roots.push(n);
                assert(!varToSubstNode.has(keys[i]));
                varToSubstNode.insert(keys[i], n);
                while (queue.size() > 0) {
                    SubstNode* var = queue.last();
                    PTRef var_tr = var->tr;
                    if (seen[getPterm(var_tr).getId()] == white) {
                        seen[getPterm(var_tr).getId()] = black;
                        for (int j = 0; j < var->children.size(); j++) {
                            SubstNode* cn = NULL;
                            if (varToSubstNode.has(var->children[j])) {
                                cn = varToSubstNode[var->children[j]];
                                if (cn->parent == NULL && cn != n) cn->parent = var;
                            } else if (substs.has(var->children[j]) && substs[var->children[j]].sgn == l_True) {
                                cn = new SubstNode(var->children[j], substs[var->children[j]].tr, var, *this);
                                alloced.push(cn);
                                queue.push(cn);
                                varToSubstNode.insert(cn->tr, cn);
                            }
                            var->child_nodes.push(cn);
                        }
                        continue;
                    } else if (seen[getPterm(var_tr).getId()] == black) {
                        queue.pop();
                        continue;
                    }
                }
            }
        }

        for (int i = 0; i < seen.size(); i++)
            seen[i] = white;

        // Find the start nodes
        vec<SubstNode*> startNodes;
        for (int i = 0; i < roots.size(); i++) {
            SubstNode* n = roots[i];
            while (n->parent != NULL) {
                n = n->parent;
            }
            startNodes.push(n);
        }
        sort(startNodes);
        int i, j;
        SubstNode* p = NULL;
        for (i = j = 0; i < startNodes.size(); i++)
            if (startNodes[i] != p)
                p = startNodes[j++] = startNodes[i];
        startNodes.shrink(i-j);

        vec<vec<PTRef> > loops;
        for (int i = 0; i < startNodes.size(); i++) {
            TarjanAlgorithm tarjan(*this);
            tarjan.getLoops(startNodes[i], loops);
        }

#ifdef SIMPLIFY_DEBUG
        if (loops.size() == 0)
            cerr << "No loops\n";
        for (int i = 0; i < loops.size(); i++) {
            cerr << "Loop " << i << endl;
            vec<PTRef>& loop = loops[i];
            for (int j = 0; j < loop.size(); j++)
                cerr << "  " << printTerm(loop[j]) << endl;
        }

        // Debug: visualize a bit.
        char* fname = NULL;
        asprintf(&fname, "loopbreak-%d.dot", iters);
        FILE* foo = fopen(fname, "w");
        free(fname);
        fprintf(foo, "digraph foo {\n");
        for (int i = 0; i < startNodes.size(); i++)
            fprintf(foo, "  %s [shape=box]\n", printTerm(startNodes[i]->tr));

        for (int i = 0; i < roots.size(); i++) {
            if (seen[getPterm(roots[i]->tr).getId()] != white)
                continue;
            vec<SubstNode*> queue;
            queue.push(roots[i]);
            while (queue.size() > 0) {
                SubstNode* n = queue.last(); queue.pop();
                if (seen[getPterm(n->tr).getId()] != white)
                    continue;
                seen[getPterm(n->tr).getId()] = black;
                for (int j = 0; j < n->child_nodes.size(); j++) {
                    if (n->child_nodes[j] != NULL) {
                        fprintf(foo, "  %s -> %s;\n", printTerm(n->tr), printTerm(n->child_nodes[j]->tr));
                        queue.push(n->child_nodes[j]);
                    }
                }
            }
        }
        for (int i = 0; i < loops.size(); i++)
            for (int j = 0; j < loops[i].size(); j++)
                fprintf(foo, "  %s -> %s [style=dotted];\n", printTerm(loops[i][j]), printTerm(loops[i][(j+1)%loops[i].size()]));
        fprintf(foo, "}");
        fclose(foo);
#endif

        // Terminate if no loops found
        if (loops.size() == 0)
            break;

        // Break the found loops
        for (int i = 0; i < loops.size(); i++) {
            substs[loops[i][0]].sgn = l_False;
        }
    }
    for (int i = 0; i < alloced.size(); i++)
        delete alloced[i];
}

//
// The substitutions for the term riddance from osmt1
//
lbool Logic::retrieveSubstitutions(vec<PtAsgn>& facts, Map<PTRef,PtAsgn,PTRefHash>& substs)
{
    for (int i = 0; i < facts.size(); i++) {
        PTRef tr = facts[i].tr;
        lbool sgn = facts[i].sgn;
        // Join equalities
        if (isEquality(tr) && sgn == l_True) {
#ifdef SIMPLIFY_DEBUG
            cerr << "Identified an equality: " << printTerm(tr) << endl;
#endif
            Pterm& t = getPterm(tr);
            // n will be the reference
            if (isUFEquality(tr) || isIff(tr)) {
                // This is the simple replacement to elimiate enode terms where possible
                assert(t.size() == 2);
                // One of them should be a var
                Pterm& a1 = getPterm(t[0]);
                Pterm& a2 = getPterm(t[1]);
                if (a1.size() == 0 || a2.size() == 0) {
                    PTRef var = a1.size() == 0 ? t[0] : t[1];
                    PTRef trm = a1.size() == 0 ? t[1] : t[0];
                    if (contains(trm, var)) continue;
                    if (isConstant(var)) {
                        assert(!isConstant(trm));
                        PTRef tmp = var;
                        var = trm;
                        trm = tmp;
                    }
#ifdef SIMPLIFY_DEBUG
                    if (substs.contains(var)) {
                        cerr << "Double substitution:" << endl;
                        cerr << " " << printTerm(var) << "/" << printTerm(trm) << endl;
                        cerr << " " << printTerm(var) << "/" << printTerm(substs[var].tr) << endl;
                        if (substs[var].sgn == l_False)
                            cerr << "  disabled" << endl;
                    } else {
                        char* tmp1 = printTerm(var);
                        char* tmp2 = printTerm(trm);
                        cerr << "Substituting " << tmp1 << " with " << tmp2 << endl;
                        ::free(tmp1); ::free(tmp2);
                    }
#endif
                    if (!substs.has(var)) {
                        substs.insert(var, PtAsgn(trm, l_True));
                    }
                }
            }
        } else if (isBoolAtom(tr)) {
            PTRef term = sgn == l_True ? getTerm_true() : getTerm_false();
            if (substs.has(tr)) {
                if (term != substs[tr].tr) return l_False;
            } else substs.insert(tr, PtAsgn(term, l_True));
        }
    }
    breakSubstLoops(substs);
    return l_Undef;
}

//
// TODO: Also this should most likely be dependent on the theory being
// used.  Depending on the theory a fact should either be added on the
// top level or left out to reduce e.g. simplex matrix size.
//
void Logic::collectFacts(PTRef root, vec<PtAsgn>& facts)
{
    Map<PTRef,bool,PTRefHash> isdup;
    vec<PtAsgn> queue;
    PTRef p;
    lbool sign;
    purify(root, p, sign);
    queue.push(PtAsgn(p, sign));

    while (queue.size() != 0) {
        PtAsgn pta = queue.last(); queue.pop();

        if (isdup.has(pta.tr)) continue;
        isdup.insert(pta.tr, true);

        Pterm& t = getPterm(pta.tr);

        if (isAnd(pta.tr) and pta.sgn == l_True)
            for (int i = 0; i < t.size(); i++) {
                PTRef c;
                lbool c_sign;
                purify(t[i], c, c_sign);
                queue.push(PtAsgn(c, pta.sgn == l_True ? c_sign : c_sign^true));
            }
        else if (isOr(pta.tr) and (pta.sgn == l_False))
            for (int i = 0; i < t.size(); i++) {
                PTRef c;
                lbool c_sign;
                purify(t[i], c, c_sign);
                queue.push(PtAsgn(c, c_sign^true));
            }
        // unary and negated
        else if (isAnd(pta.tr) and (pta.sgn == l_False) and (t.size() == 1)) {
            PTRef c;
            lbool c_sign;
            purify(t[0], c, c_sign);
            queue.push(PtAsgn(c, c_sign^true));
        }
        // unary or
        else if (isOr(pta.tr) and (pta.sgn == l_True) and (t.size() == 1)) {
            PTRef c;
            lbool c_sign;
            purify(t[0], c, c_sign);
            queue.push(PtAsgn(c, c_sign));
        }
        // Found a fact.  It is important for soundness that we have also the original facts
        // asserted to the euf solver in the future even though no search will be performed there.
        else if (isEquality(pta.tr) and pta.sgn == l_True) {
            facts.push(pta);
        }
        else if (isUP(pta.tr) and pta.sgn == l_True) {
            facts.push(pta);
        }
        else if (isXor(pta.tr) and pta.sgn == l_True) {
            Pterm& t = getPterm(pta.tr);
            facts.push(PtAsgn(mkEq(t[0], mkNot(t[1])), l_True));
        }
        else {
            PTRef c;
            lbool c_sign;
            purify(pta.tr, c, c_sign);
            if (isBoolAtom(c)) {
                facts.push(PtAsgn(c, c_sign^(pta.sgn == l_False)));
            }
        }
    }

#ifdef SIMPLIFY_DEBUG
    cerr << "True facts" << endl;
    for (int i = 0; i < facts.size(); i++)
        cerr << (facts[i].sgn == l_True ? "" : "not ") << printTerm(facts[i].tr) << " (" << facts[i].tr.x << ")" << endl;
#endif
}

//
// Does term contain var?  (works even if var is a term...)
//
bool Logic::contains(PTRef term, PTRef var)
{
    Map<PTRef, bool, PTRefHash> proc;
    vec<PTRef> queue;
    queue.push(term);

    while (queue.size() != 0) {
        PTRef tr = queue.last();
        if (tr == var) return true;
        if (proc.has(tr)) {
            queue.pop();
            continue;
        }
        bool unprocessed_children = false;
        Pterm& t = getPterm(tr);
        for (int i = 0; i < t.size(); i++)
            if (!proc.has(t[i])) {
                queue.push(t[i]);
                unprocessed_children = true; }
        if (unprocessed_children) continue;
        queue.pop();
        proc.insert(tr, true);
    }
    return false;
}

//
// Get all vars from a term
//
void Logic::getVars(PTRef term, vec<PTRef>& vars) const
{
    Map<PTRef, bool, PTRefHash> proc;
    vec<PTRef> queue;
    queue.push(term);

    while (queue.size() != 0) {
        PTRef tr = queue.last();
        if (proc.has(tr)) {
            queue.pop();
            continue;
        }
        bool unprocessed_children = false;
        const Pterm& t = getPterm(tr);
        for (int i = 0; i < t.size(); i++)
            if (!proc.has(t[i])) {
                queue.push(t[i]);
                unprocessed_children = true; }
        if (unprocessed_children) continue;
        queue.pop();
        proc.insert(tr, true);
        if (isVar(tr)) vars.push(tr);
    }
}

PTRef Logic::learnEqTransitivity(PTRef formula)
{
    vec<PTRef> implications;
    vec<PTRef> queue;
    Map<PTRef,bool,PTRefHash> processed;

    queue.push(formula);
    while (queue.size() != 0) {
        PTRef tr = queue.last();
        if (processed.has(tr)) {
            queue.pop(); continue; }

        Pterm& t = getPterm(tr);
        bool unp_ch = false;
        for (int i = 0; i < t.size(); i++) {
            if (!processed.has(t[i])) {
                queue.push(t[i]);
                unp_ch = true;
            }
        }
        if (unp_ch) continue;

        queue.pop();
        //
        // Add (or (and (= x w) (= w z)) (and (= x y) (= y z))) -> (= x z)
        //

        const bool cond1 = isOr(tr) && t.size() == 2 &&
                           isAnd(t[0]) && isAnd(t[1]) &&
                           isEquality(getPterm(t[0])[0]) &&
                           isEquality(getPterm(t[0])[1]) &&
                           isEquality(getPterm(t[1])[0]) &&
                           isEquality(getPterm(t[1])[1]);

        if (cond1) {
            // (= v1 v2) (= v3 v4)
            PTRef v1 = getPterm(getPterm(t[0])[0])[0];
            PTRef v2 = getPterm(getPterm(t[0])[0])[1];
            PTRef v3 = getPterm(getPterm(t[0])[1])[0];
            PTRef v4 = getPterm(getPterm(t[0])[1])[1];

            // (= t1 t2) (= t3 t4)
            PTRef t1 = getPterm(getPterm(t[1])[0])[0];
            PTRef t2 = getPterm(getPterm(t[1])[0])[1];
            PTRef t3 = getPterm(getPterm(t[1])[1])[0];
            PTRef t4 = getPterm(getPterm(t[1])[1])[1];

            // Detecting bridging variables
            const bool cond2a = v1 == v3 || v1 == v4 || v2 == v3 || v2 == v4;
            const bool cond2b = t1 == t3 || t1 == t4 || t2 == t3 || t2 == t4;

            if (cond2a && cond2b) {
                PTRef w  = (v1 == v3 || v1 == v4 ? v1 : v2);
                PTRef x1 = (v1 == w ? v2 : v1);
                PTRef z1 = (v3 == w ? v4 : v3);

                PTRef y  = (t1 == t3 || t1 == t4 ? t1 : t2);
                PTRef x2 = (t1 == y ? t2 : t1);
                PTRef z2 = (t3 == y ? t4 : t3);

                const bool cond2 = (x1 == x2 && z1 == z2) || (x1 == z2 && x2 == z1);
                if (cond2) {
                    vec<PTRef> args_eq;
                    args_eq.push(x1);
                    args_eq.push(z1);
                    PTRef eq = mkEq(args_eq);
                    vec<PTRef> args_impl;
                    args_impl.push(tr);
                    args_impl.push(eq);
                    PTRef impl = mkImpl(args_impl);
                    implications.push(impl);
                }
            }
        }
        processed.insert(tr, true);
    }

    if (implications.size() > 0)
        return mkAnd(implications);
    else
        return PTRef_Undef;
}


//
// Logic data contains the maps for equalities, disequalities and ites
// +-----------------------------------+
// |size|eqs_offs|diseqs_offs|ites_offs|
// +----+---+----+-----------+---------+
// |eqs_size| <eqs_data>               |
// +--------+--+-----------------------+
// |diseqs_size| <diseqs_data>         |
// +---------+-+-----------------------+
// |ites_size| <ites_data>             |
// +---------+-------------------------+
//
void Logic::serializeLogicData(int*& logicdata_buf) const
{
    int equalities_sz    = 1;
    int disequalities_sz = 1;
    int ites_sz          = 1;

    const vec<SymRef> &symbols = sym_store.getSymbols();
    for (int i = 0; i < symbols.size(); i++) {
        if (equalities.has(symbols[i]))
            equalities_sz ++;
        if (disequalities.has(symbols[i]))
            disequalities_sz ++;
        if (ites.has(symbols[i]))
            ites_sz ++;
    }

    int logicdata_sz = equalities_sz + disequalities_sz + ites_sz + 4;
    logicdata_buf = (int*) malloc(logicdata_sz*sizeof(int));
    logicdata_buf[buf_sz_idx] = logicdata_sz;
    int equalities_offs = 4;
    int disequalities_offs = equalities_offs + equalities_sz;
    int ites_offs = disequalities_offs + disequalities_sz;

    logicdata_buf[equalities_offs_idx] = equalities_offs;
    logicdata_buf[disequalities_offs_idx] = disequalities_offs;
    logicdata_buf[ites_offs_idx] = ites_offs;

    logicdata_buf[equalities_offs] = equalities_sz;
    logicdata_buf[disequalities_offs] = disequalities_sz;
    logicdata_buf[ites_offs] = ites_sz;

    int equalities_p = equalities_offs+1;
    int disequalities_p = disequalities_offs+1;
    int ites_p = ites_offs+1;
    for (int i = 0; i < symbols.size(); i++) {
        if (equalities.has(symbols[i]))
            logicdata_buf[equalities_p ++] = symbols[i].x;
        if (disequalities.has(symbols[i]))
            logicdata_buf[disequalities_p ++] = symbols[i].x;
        if (ites.has(symbols[i]))
            logicdata_buf[ites_p ++] = symbols[i].x;
    }
}

void Logic::deserializeLogicData(const int* logicdata_buf)
{
    const int* eqs_buf = &logicdata_buf[logicdata_buf[equalities_offs_idx]];
    const int* diseqs_buf = &logicdata_buf[logicdata_buf[disequalities_offs_idx]];
    const int* ites_buf = &logicdata_buf[logicdata_buf[ites_offs_idx]];

    int eqs_sz = eqs_buf[0];
    for (int i = 0; i < eqs_sz-1; i++) {
        SymRef sr = {(uint32_t)eqs_buf[i+1]};
        if (!equalities.has(sr))
            equalities.insert(sr, true);
    }

    int diseqs_sz = diseqs_buf[0];
    for (int i = 0; i < diseqs_sz - 1; i++) {
        SymRef sr = {(uint32_t)diseqs_buf[i+1]};
        if (!disequalities.has(sr))
            disequalities.insert(sr, true);
    }

    int ites_sz = ites_buf[0];
    for (int i = 0; i < ites_sz - 1; i++) {
        SymRef sr = {(uint32_t)ites_buf[i+1]};
        if (!ites.has(sr))
            ites.insert(sr, true);
    }
}

void Logic::serializeTermSystem(int*& termstore_buf, int*& symstore_buf, int*& idstore_buf, int*& sortstore_buf, int*& logicdata_buf) const
{
    idstore_buf   = id_store.serializeIdentifiers();
    sortstore_buf = sort_store.serializeSorts();
    symstore_buf  = sym_store.serializeSymbols();
    termstore_buf = term_store.serializeTerms();
    serializeLogicData(logicdata_buf);
}

void Logic::deserializeTermSystem(const int* termstore_buf, const int* symstore_buf, const int* idstore_buf, const int* sortstore_buf, const int* logicdata_buf)
{
    id_store.deserializeIdentifiers(idstore_buf);
    sort_store.deserializeSorts(sortstore_buf);
    sym_store.deserializeSymbols(symstore_buf);
    term_store.deserializeTerms(termstore_buf);
    deserializeLogicData(logicdata_buf);
}

void
Logic::dumpChecksatToFile(ostream& dump_out)
{
    dump_out << "(check-sat)" << endl;
    dump_out << "(exit)" << endl;
}

void
Logic::dumpHeaderToFile(ostream& dump_out)
{
    dump_out << "(set-logic " << getName() << ")" << endl;

    const vec<SRef>& sorts = sort_store.getSorts();
    for (int i = 0; i < sorts.size(); i++)
    {
        if (isBuiltinSort(sorts[i])) continue;
        dump_out << "(declare-sort " << sort_store.getName(sorts[i]) << " 0)" << endl;
    }

    const vec<SymRef>& symbols = sym_store.getSymbols();
    for(int i = 0; i < symbols.size(); ++i)
    {
        SymRef s = symbols[i];
        if (!isUF(s) && !isVar(s)) continue;
        if (isConstant(s)) continue;
        char* sym = printSym(s);
        dump_out << "(declare-fun " << sym << " ";
        free(sym);
        Symbol& symb = sym_store[s];
        dump_out << "(";
        for(int j = 0; j < symb.nargs(); ++j)
        {
            dump_out << sort_store.getName(symb[j]) << " ";
        }
        dump_out << ") " << sort_store.getName(symb.rsort()) << ")" << endl;
    }
}

void
Logic::dumpFormulaToFile( ostream & dump_out, PTRef formula, bool negate, bool toassert )
{
    vector< PTRef > unprocessed_enodes;
    map< PTRef, string > enode_to_def;
    unsigned num_lets = 0;

    unprocessed_enodes.push_back( formula );
    // Open assert
    if(toassert)
        dump_out << "(assert" << endl;
    //
    // Visit the DAG of the formula from the leaves to the root
    //
    while( !unprocessed_enodes.empty( ) )
    {
        PTRef e = unprocessed_enodes.back( );
        //
        // Skip if the node has already been processed before
        //
        if ( enode_to_def.find( e ) != enode_to_def.end( ) )
        {
            unprocessed_enodes.pop_back( );
            continue;
        }

        bool unprocessed_children = false;
        Pterm& term = getPterm(e);
        for(int i = 0; i < term.size(); ++i)
        {
            PTRef pref = term[i];
            //assert(isTerm(pref));
            //
            // Push only if it is unprocessed
            //
            if ( enode_to_def.find( pref ) == enode_to_def.end( ) && (isBooleanOperator( pref ) || isEquality(pref)))
            {
                unprocessed_enodes.push_back( pref );
                unprocessed_children = true;
            }
        }
        //
        // SKip if unprocessed_children
        //
        if ( unprocessed_children ) continue;

        unprocessed_enodes.pop_back( );

        char buf[ 32 ];
        sprintf( buf, "?def%d", getPterm(e).getId() );

        // Open let
        dump_out << "(let ";
        // Open binding
        dump_out << "((" << buf << " ";

        if (term.size() > 0 ) dump_out << "(";
        char* sym = printSym(term.symb());
        dump_out << printSym(term.symb());
        free(sym);
        for (int i = 0; i < term.size(); ++i)
        {
            PTRef pref = term[i];
            if ( isBooleanOperator(pref) || isEquality(pref) )
                dump_out << " " << enode_to_def[ pref ];
            else
            {
                dump_out << " " << printTerm(pref);
                if ( isAnd(e) ) dump_out << endl;
            }
        }
        if ( term.size() > 0 ) dump_out << ")";

        // Closes binding
        dump_out << "))" << endl;
        // Keep track of number of lets to close
        num_lets++;

        assert( enode_to_def.find( e ) == enode_to_def.end( ) );
        enode_to_def[ e ] = buf;
    }
    dump_out << endl;
    // Formula
    if ( negate ) dump_out << "(not ";
    dump_out << enode_to_def[ formula ] << endl;
    if ( negate ) dump_out << ")";
    // Close all lets
    for ( unsigned n=1; n <= num_lets; n++ ) dump_out << ")";
    // Closes assert
    if(toassert)
        dump_out << ")" << endl;
}

void
Logic::dumpFunction(ostream& dump_out, Tterm *function)
{
    dump_out << "(define-fun " << function->getName() << " ( ";
    vec<PTRef>& args = function->getArgs();
    for(int i = 0; i < args.size(); ++i)
        dump_out << '(' << getSymName(args[i]) << ' ' <<  getSortName(getSortRef(args[i])) << ") ";
    dump_out << ") Bool (";
    dumpFormulaToFile(dump_out, function->getBody(), false, false);
    dump_out << "))" << endl;
}

PTRef
Logic::instantiateFunctionTemplate(Tterm& templ, map<PTRef, PTRef> subst)
{
    return PTRef_Undef;
}

#ifdef PRODUCE_PROOF

bool
Logic::implies(PTRef implicant, PTRef implicated)
{
    Logic& logic = *this;
    const char * implies = "implies.smt2";
    std::ofstream dump_out( implies );
    logic.dumpHeaderToFile(dump_out);

    logic.dumpFormulaToFile(dump_out, implicant);
    logic.dumpFormulaToFile(dump_out, implicated, true);
    dump_out << "(check-sat)" << endl;
    dump_out << "(exit)" << endl;
    dump_out.close( );
    // Check !
    bool tool_res;
    if ( int pid = fork() )
    {
      int status;
      waitpid(pid, &status, 0);
      switch ( WEXITSTATUS( status ) )
      {
	case 0:
	  tool_res = false;
	  break;
	case 1:
	  tool_res = true;
	  break;
	default:
	  perror( "Tool" );
	  exit( EXIT_FAILURE );
      }
    }
    else
    {
      execlp( "tool_wrapper.sh", "tool_wrapper.sh", implies, NULL );
      perror( "Tool" );
      exit( 1 );
    }

    if ( tool_res == true )
        return false;
    return true;
}

bool
Logic::verifyInterpolantA(PTRef itp, const ipartitions_t& mask)
{
    // Check A -> I, i.e., A & !I
    return implies(getPartitionA(mask), itp);
}

PTRef
Logic::getPartitionA(const ipartitions_t& mask)
{
    Logic& logic = *this;
    vec<PTRef>& ass = logic.getAssertions();
    vec<PTRef> a_args;
    for(int i = 0; i < ass.size(); ++i)
    {
        PTRef a = ass[i];
    	ipartitions_t p = 0;
	    setbit(p, i + 1);
        if(isAstrict(p, mask)) a_args.push(a);
        else if(isBstrict(p, mask)) {}
    	else opensmt_error("Assertion is neither A or B");
    }
    PTRef A = logic.mkAnd(a_args);
    return A;
}

PTRef
Logic::getPartitionB(const ipartitions_t& mask)
{
    Logic& logic = *this;
    vec<PTRef>& ass = logic.getAssertions();
    vec<PTRef> b_args;
    for(int i = 0; i < ass.size(); ++i)
    {
        PTRef a = ass[i];
    	ipartitions_t p = 0;
	    setbit(p, i + 1);
        if(isAstrict(p, mask)) {}
        else if(isBstrict(p, mask)) b_args.push(a);
    	else opensmt_error("Assertion is neither A or B");
    }
    PTRef B = logic.mkAnd(b_args);
    return B;
}

bool
Logic::verifyInterpolantB(PTRef itp, const ipartitions_t& mask)
{
    Logic& logic = *this;
    PTRef nB = logic.mkNot(getPartitionB(mask));
    // Check A -> I, i.e., A & !I
    return implies(itp, nB);
}

bool
Logic::verifyInterpolant(PTRef itp, const ipartitions_t& mask)
{
    if(verbose())
        cout << "; Verifying final interpolant" << endl;
    bool res = verifyInterpolantA(itp, mask);
    if(!res)
        opensmt_error("A -> I does not hold");
    if(verbose())
        cout << "; A -> I holds" << endl;
    res = verifyInterpolantB(itp, mask);
    if(!res)
        opensmt_error("I -> !B does not hold");
    if(verbose())
        cout << "; B -> !I holds" << endl;
    return res;
}

void
Logic::addVarClassMask(Var l, const ipartitions_t& toadd)
{
	opensmt::orbit(var_class[l], var_class[l], toadd);
#ifdef ITP_DEBUG
	cerr << "; Adding mask " << toadd << " to var " << l << endl;
	cerr << "; Var " << l << " now has mask " << var_class[l] << endl;
#endif
}

void
Logic::addClauseClassMask(CRef l, const ipartitions_t& toadd)
{
	opensmt::orbit(clause_class[l], clause_class[l], toadd);
#ifdef ITP_DEBUG
	cerr << "; Adding mask " << toadd << " to clause " << l << endl;
	cerr << "; Clause " << l << " now has mask " << clause_class[l] << endl;
#endif
}

void
Logic::setIPartitionsIte(PTRef pref)
{
    set<PTRef> visited;
    queue<PTRef> bfs;
    bool unprocessed_children;
    bfs.push(pref);
    while(!bfs.empty())
    {
        PTRef p = bfs.front();
        bfs.pop();
        if(visited.find(p) != visited.end()) continue;
        
        // fine to visit
        visited.insert(p);
        if(isUF(p) || isUP(p))
        {
            addIPartitions(getPterm(p).symb(), getIPartitions(pref));
        }
        if (p != pref)
        {
            addIPartitions(p, getIPartitions(pref));
        }

        // set on children
        Pterm& t = getPterm(p);
        unprocessed_children = false;
        for(int i = 0; i < t.size(); ++i)
        {
            PTRef c = t[i];
            if(visited.find(c) == visited.end())
            {
                bfs.push(c);
                unprocessed_children = true;
            }
        }
    }
}
#endif

//bool Logic::DeclareSort(string& name, int arity) {
//    printf("Declaring sort %s of arity %d\n", name.c_str(), arity);
//    sstore.newSymbol(name.c_str());
//    return true;
//}

//bool Logic::DeclareFun(string& name, list<Sort*>& args, Sort& rets) {
//    printf("Declaring function %s of ", name.c_str());
//    if (args.empty())
//        printf("no arguments ");
//    else {
//        printf("arguments ");
//        for (list<Sort*>::iterator it = args.begin(); it != args.end(); it++)
//            printf("%s ", (**it).toString()->c_str());
//    }
//    printf("and return sort %s\n", rets.toString()->c_str());
//
//    egraph.newSymbol(name.c_str(), args, rets)
//    return true;
//}


void
Logic::collectStats(PTRef root, int& n_of_conn, int& n_of_eq, int& n_of_uf)
{
    set<PTRef> seen_terms;
    queue<PTRef> to_visit;
    n_of_conn = n_of_eq = n_of_uf = 0;
    to_visit.push(root);
    while(!to_visit.empty())
    {
        PTRef node = to_visit.front();
        to_visit.pop();
        if(seen_terms.find(node) != seen_terms.end()) continue;
        seen_terms.insert(node);
        if(isBooleanOperator(node))
        {
            ++n_of_conn;
            Pterm& pnode = getPterm(node);
            for(int i = 0; i < pnode.size(); ++i)
                to_visit.push(pnode[i]);
        }
        else if(isUFEquality(node))
        {
            ++n_of_eq;
            Pterm& pnode = getPterm(node);
            to_visit.push(pnode[0]);
            to_visit.push(pnode[1]);
        }
        else if(isUF(node))
        {
            ++n_of_uf;
            Pterm& pnode = getPterm(node);
            for(int i = 0; i < pnode.size(); ++i)
                to_visit.push(pnode[i]);
        }
    }
}

