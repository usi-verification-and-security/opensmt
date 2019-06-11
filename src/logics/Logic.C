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
#include "SMTConfig.h"
#include <queue>
#include <set>

#include <sys/wait.h>


using namespace std;

/***********************************************************
 * Class defining logic
 ***********************************************************/

const char* Logic::e_argnum_mismatch = "incorrect number of arguments";
const char* Logic::e_bad_constant    = "incorrect constant for logic";

const char* Logic::tk_val_uf_default   = "UFDefault";
const char* Logic::tk_val_bool_default = "true";

const char* Logic::tk_true     = "true";
const char* Logic::tk_false    = "false";
const char* Logic::tk_anon     = ".anon";
const char* Logic::tk_not      = "not";
const char* Logic::tk_uf_not   = ".uf-not";
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
    , sort_store(id_store)
    , term_store(sym_store, sort_store)
    , sym_TRUE(SymRef_Undef)
    , sym_FALSE(SymRef_Undef)
    , sym_ANON(SymRef_Undef)
    , sym_AND(SymRef_Undef)
    , sym_OR(SymRef_Undef)
    , sym_XOR(SymRef_Undef)
    , sym_NOT(SymRef_Undef)
    , sym_UF_NOT(SymRef_Undef)
    , sym_EQ(SymRef_Undef)
    , sym_IMPLIES(SymRef_Undef)
    , sym_DISTINCT(SymRef_Undef)
    , sym_ITE(SymRef_Undef)
    , sort_BOOL(SRef_Undef)
    , term_TRUE(PTRef_Undef)
    , term_FALSE(PTRef_Undef)
    , subst_num(0)
{
    logic_type = opensmt::Logic_t::QF_UF;
    config.logic = logic_type;

    char* msg;
    // We can't use declareSort here since it assumes that sort_BOOL
    // exists for making the equality symbol!
    IdRef bool_id = id_store.newIdentifier("Bool");
    vec<SRef> tmp_srefs;
    sort_store.newSort(bool_id, tmp_srefs);
    sort_BOOL = sort_store["Bool"];

    term_TRUE = mkConst(getSort_bool(), tk_true);
    if (term_TRUE == PTRef_Undef) {
        printf("Error in constructing term %s: %s\n", tk_true, msg);
        assert(false);
    }
    sym_TRUE = sym_store.nameToRef(tk_true)[0];
    sym_store[sym_TRUE].setNoScoping();
    sym_store.setInterpreted(sym_TRUE);


    term_FALSE = mkConst(getSort_bool(), tk_false);
    if (term_FALSE  == PTRef_Undef) {
        printf("Error in constructing term %s: %s\n", tk_false, msg);
        assert(false);
    }
    sym_FALSE = sym_store.nameToRef(tk_false)[0];
    sym_store[sym_FALSE].setNoScoping();
    sym_store.setInterpreted(sym_FALSE);

    // The anonymous symbol for the enodes of propositional formulas nested inside UFs (or UPs)
    vec<SRef> params;
    sym_ANON = sym_store.newSymb(tk_anon, params, &msg);

    params.push(sort_BOOL);

    // UF not that is not visible outside the uf solver
    sym_UF_NOT = sym_store.newSymb(tk_uf_not, params, &msg);


    if ((sym_NOT = declareFun(tk_not, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_not, msg);
        assert(false);
    }
    sym_store[sym_NOT].setNoScoping();
    sym_store.setInterpreted(sym_NOT);

    params.push(sort_BOOL);

    if ((sym_EQ = declareFun(tk_equals, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_equals, msg);
        assert(false);
    }
    if (sym_store[sym_EQ].setChainable() == false) { assert(false); }
    sym_store[sym_EQ].setNoScoping();
    sym_store[sym_EQ].setCommutes();
    equalities.insert(sym_EQ, true);
    sym_store.setInterpreted(sym_EQ);

    if ((sym_IMPLIES = declareFun(tk_implies, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_implies, msg);
        assert(false);
    }
    if (sym_store[sym_IMPLIES].setRightAssoc() == false) { assert(false); }
    sym_store[sym_IMPLIES].setNoScoping();
    sym_store.setInterpreted(sym_IMPLIES);

    if ((sym_AND = declareFun(tk_and, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_and, msg);
        assert(false);
    }
    if (sym_store[sym_AND].setLeftAssoc() == false) { assert(false); }
    sym_store[sym_AND].setNoScoping();
    sym_store[sym_AND].setCommutes();
    sym_store.setInterpreted(sym_AND);

    if ((sym_OR = declareFun(tk_or, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_or, msg);
        assert(false);
    }
    if (sym_store[sym_OR].setLeftAssoc() == false) { assert(false); }
    sym_store[sym_OR].setNoScoping();
    sym_store[sym_OR].setCommutes();
    sym_store.setInterpreted(sym_OR);

    if ((sym_XOR = declareFun(tk_xor, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_xor, msg);
        assert(false);
    }
    if (sym_store[sym_XOR].setLeftAssoc() == false) { assert(false); }
    sym_store[sym_XOR].setNoScoping();
    sym_store[sym_XOR].setCommutes();
    sym_store.setInterpreted(sym_OR);

    if ((sym_DISTINCT = declareFun(tk_distinct, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_distinct, msg);
        assert(false);
    }
    if (sym_store[sym_DISTINCT].setPairwise() == false) { assert(false); }
    sym_store[sym_DISTINCT].setNoScoping();
    sym_store[sym_DISTINCT].setCommutes();
    disequalities.insert(sym_DISTINCT, true);
    sym_store.setInterpreted(sym_DISTINCT);

    if ((sym_ITE = declareFun(tk_ite, sort_BOOL, params, &msg, true)) == SymRef_Undef) {
        printf("Error in declaring function %s: %s\n", tk_ite, msg);
        assert(false);
    }
    if (sym_store[sym_ITE].setLeftAssoc() == false) { assert(false); }
    sym_store[sym_ITE].setNoScoping();
    sym_store.setInterpreted(sym_ITE);

    ites.insert(sym_ITE, true);

#ifdef PRODUCE_PROOF
    ipartitions_t mask = 0;
    mask = ~mask;
    setIPartitions(getTerm_true(), mask);
    setIPartitions(getTerm_false(), mask);
#endif
}

bool Logic::isBuiltinFunction(const SymRef sr) const
{
    if (sr == sym_TRUE || sr == sym_FALSE || sr == sym_AND || sr == sym_OR || sr == sym_XOR || sr == sym_NOT || sr == sym_EQ || sr == sym_IMPLIES || sr == sym_DISTINCT || sr == sym_ITE) return true;
    if (isEquality(sr) || isDisequality(sr)) return true;
    return false;
}

Logic::~Logic()
{
#ifdef STATISTICS
    cerr << "; -------------------------\n";
    cerr << "; STATISTICS FOR LOGICS\n";
    cerr << "; -------------------------\n";
    cerr << "; Substitutions............: " << subst_num << endl;
#endif // STATISTICS
}

const opensmt::Logic_t
Logic::getLogic() const
{
    return logic_type;
}

const char*
Logic::getName() const
{
    return "QF_UF";
}

//
// Escape the symbol name if it contains a prohibited character from the
// list defined by the quotable[] table below
//
bool Logic::hasQuotableChars(const char* name) const
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
        0, 1, 0, 1, 0, 0, 1, 0, 0, 0, // [, \, ], `
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
    bool quoted = false;
    bool escape = false;
    char first = name[0];
    char last;
    for (int i = 0; name[i] != '\0'; i++)
    {
        if (quotable[(int)name[i]])
            escape = true;
        last = name[i];
    }
    quoted = (first == '|') && (last == '|');
    if (!quoted && escape)
        return true;
    else
        return false;
}

//
// Quote the name if it contains illegal characters
//
char*
Logic::protectName(const char* name) const
{
    char *name_escaped;
    int printed_chars = hasQuotableChars(name) ? asprintf(&name_escaped, "|%s|", name)
            : asprintf(&name_escaped, "%s", name);
    (void)printed_chars;
    return name_escaped;
}

char*
Logic::printSym(SymRef sr) const
{
    return protectName(sym_store.getName(sr));
}

char*
Logic::pp(PTRef tr) const
{
    char* out;

    const Pterm& t = getPterm(tr);
    SymRef sr = t.symb();
    std::string name_escaped = printSym(sr);

    if (t.size() == 0) {
        std::stringstream ss;
        ss << name_escaped;
#ifdef PARTITION_PRETTYPRINT
        ss << " [" << getIPartitions(tr) << ' ]';
#endif
        out = strdup(ss.str().c_str());
        return out;
    }

    // Here we know that t.size() > 0

    std::stringstream ss;
    ss << '(' << name_escaped << ' ';
    for (int i = 0; i < t.size(); i++) {
        const std::string arg = pp(t[i]);
        ss << arg;
        if (i < t.size()-1) {
            ss << ' ';
        }
    }
    ss << ')';
#ifdef PARTITION_PRETTYPRINT
    ss << " [" << getIPartitions(tr) << ']';
#endif
    out = strdup(ss.str().c_str());
    return out;
}

char*
Logic::printTerm_(PTRef tr, bool ext, bool safe) const
{
    char* out;

    if (safe && this->isIteVar(tr)) {
        Ite ite = top_level_ites[tr];
        char *str_i = printTerm_(ite.i, ext, safe);
        char *str_t = printTerm_(ite.t, ext, safe);
        char *str_e = printTerm_(ite.e, ext, safe);

        int res = asprintf(&out, "(ite %s %s %s)", str_i, str_t, str_e);
        assert(res >= 0); (void)res;

        free(str_i); free(str_t); free(str_e);

        return out;
    }

    const Pterm& t = getPterm(tr);
    SymRef sr = t.symb();
    char* name_escaped = printSym(sr);

    if (t.size() == 0) {
        int res = ext ? asprintf(&out, "%s <%d>", name_escaped, tr.x)
                : asprintf(&out, "%s", name_escaped);
        assert(res >= 0); (void)res;
        free(name_escaped);
        return out;
    }

    // Here we know that t.size() > 0

    char* old;
    int chars_written = asprintf(&out, "(%s ", name_escaped);
    assert(chars_written >= 0);
    free(name_escaped);

    for (int i = 0; i < t.size(); i++) {
        old = out;
        char * current_term = printTerm_(t[i], ext, safe);
        chars_written = asprintf(&out, "%s%s", old, current_term);
        assert(chars_written >= 0);
        ::free(old);
        ::free(current_term);
        if (i < t.size()-1) {
            old = out;
            chars_written = asprintf(&out, "%s ", old);
            assert(chars_written >= 0);
            ::free(old);
        }
    }
    old = out;
    chars_written = ext ? asprintf(&out, "%s) <%d>", old, tr.x) : asprintf(&out, "%s)", old);
    assert(chars_written >= 0); (void)chars_written;
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
    else if (hasSortBool(ptr) && appearsInUF(ptr)) {
        return true;
    }
    else
        return isTheorySymbol(sr);
}

bool Logic::isTheorySymbol(SymRef tr) const {
    // True and False are special cases, we count them as theory symbols
    if (tr == sym_TRUE || tr == sym_FALSE) return true;
    const Symbol& t = sym_store[tr];
    // Boolean var
    if (t.rsort() == sort_BOOL && t.nargs() == 0) return false;
    // Standard Boolean operators
    return !(isBooleanOperator(tr));
}

void Logic::setAppearsInUF(PTRef tr) {
    uint32_t id = Idx(getPterm(tr).getId());

    if (appears_in_uf.size() <= id || appears_in_uf[id] == false)
        propFormulasAppearingInUF.push(tr);

    while (id >= appears_in_uf.size())
        appears_in_uf.push(false);

    appears_in_uf[id] = true;
}

bool Logic::appearsInUF(PTRef tr) const {
    uint32_t id = Idx(getPterm(tr).getId());
    if (id < appears_in_uf.size())
        return appears_in_uf[id];
    else
        return false;
}

/**
 * Return all nested Boolean roots.  A PTRef tr is a nested Boolean root if it is an argument of a term f
 *  where f is not a Boolean operator and tr has a Boolean return sort.
 * @param root
 * @return
 */
vec<PTRef> Logic::getNestedBoolRoots(PTRef root) const {
    vec<PTRef> nestedBoolRoots;

    vec<PTRef> queue;
    std::unordered_set<PTRef, PTRefHash> processed;
    queue.push(root);

    while (queue.size() != 0) {
        PTRef tr = queue.last();
        queue.pop();
        if (processed.find(tr) != processed.end()) { continue; } // already processed
        const Pterm& t = getPterm(tr);
        for (int i = 0; i < t.size(); i++) {
            queue.push(t[i]);
            if (!isBooleanOperator(tr) && hasSortBool(t[i])) {
                nestedBoolRoots.push(t[i]);
            }
        }
        processed.insert(tr);
    }
    return nestedBoolRoots;
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
    ptermSort(t);
    return false;
}


void Logic::visit(PTRef tr, Map<PTRef,PTRef,PTRefHash>& tr_map)
{
    Pterm& p = getPterm(tr);
    vec<PTRef> newargs(p.size());
    char *msg;
    bool changed = false;
    for (int i = 0; i < p.size(); ++i) {
        PTRef tr = p[i];
        if (tr_map.has(tr)) {
            changed |= (tr_map[tr] != tr);
            newargs[i] = tr_map[tr];
        }
        else
            newargs[i] = tr;
    }
    if (!changed) {return;}
    PTRef trp = insertTerm(p.symb(), newargs, &msg);
    if (trp != tr) {
#ifdef PRODUCE_PROOF
    transferPartitionMembership(tr, trp);
#endif
        if (tr_map.has(tr))
            assert(tr_map[tr] == trp);
        else
            tr_map.insert(tr, trp);
    }
}


//
// XXX Comments? This method is currently under development
//
void Logic::simplifyTree(PTRef tr, PTRef& root_out)
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
            if (unprocessed_children) continue;
        }
        assert(!unprocessed_children);
#ifdef SIMPLIFY_DEBUG
        cerr << "Found a node " << queue[i].x.x << endl;
        cerr << "Before simplification it looks like " << this->printTerm(queue[i].x) << endl;
#endif
        processed.insert(queue[i].x, true);
        visit(queue[i].x, tr_map);
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
        if (defined_functions.has(s)) {
            // Make a new function by substituting the arguments of defined_functions[s] with whatever is in args
            const vec<PTRef>& tpl_args = defined_functions[s].getArgs();
            Map<PTRef,PTRef,PTRefHash> subst_map;
            if (args.size() != tpl_args.size()) {
                int written = asprintf(msg, "Arg size mismatch: should be %d but is %d", tpl_args.size(), args.size());
                assert(written >= 0); (void)written;
                return PTRef_Undef;
            }
            for (int i = 0; i < args.size(); i++) {
                if (getSortRef(args[i]) == getSortRef(tpl_args[i]))
                    subst_map.insert(tpl_args[i], args[i]);
                else {
                    int written = asprintf(msg, "Arg %s (%d) return sort mismatch: should be %s but is %s",
                            printTerm(args[i]), i, getSymName(tpl_args[i]), getSymName(args[i]));
                    assert(written >= 0); (void)written;
                    return PTRef_Undef;
                }
            }
            return instantiateFunctionTemplate(s, subst_map);
        }
        else {
            int written = asprintf(msg, "Unknown symbol `%s'", s);
            assert(written >= 0); (void)written;
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


const char*
Logic::getDefaultValue(const PTRef tr) const
{
    if (hasSortBool(tr))
        return tk_val_bool_default;
    else
        return tk_val_uf_default;
}

PTRef
Logic::mkIte(vec<PTRef>& args)
{
    if (!hasSortBool(args[0])) return PTRef_Undef;
    assert(args.size() == 3);
    if (isTrue(args[0]))    return args[1];
    if (isFalse(args[0]))   return args[2];
    if (args[1] == args[2]) return args[1];

    SRef sr = getSortRef(args[1]);
    if(sr != getSortRef(args[2]))
    {
        cerr << "ITE with different return sorts" << endl;
        assert(0);
    }

    char* name;
    static unsigned ite_counter = 0;
    int written = asprintf(&name, "%s%d", s_ite_prefix, ite_counter++);
    assert(written >= 0); (void)written;
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

    if (args.size() == 0)
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
        for (int i = 0; i < args.size(); ++i)
        {
            if (isFalse(args[i])) {
                tr = getTerm_false();
                break;
            }
            if (!isTrue(args[i]))
                newargs.push(args[i]);
        }
        if (tr == PTRef_Undef) {
            if(newargs.size() == 0)
                tr = getTerm_true();
            else if(newargs.size() == 1)
                tr = newargs[0];
            else
                tr = mkFun(getSym_and(), newargs);
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
        tr = mkFun(getSym_or(), newargs);
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
    tr = mkFun(getSym_xor(), newargs);

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
    if (isConstant(args[0]) && isConstant(args[1]))
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
    return mkFun(eq_sym, args);
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
        tr = mkFun(getSym_not(), tmp);
    }

    if(tr == PTRef_Undef) {
        printf("Error in mkNot");
        assert(0);
    }

    return tr;
}

PTRef Logic::mkConst(const char* name, const char** msg)
{
    //assert(0);
    //return PTRef_Undef;
    assert(strlen(name) > 0);
    vec<PTRef> args;
    char *msg2;
    return resolveTerm(name, args, &msg2);
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

PTRef Logic::mkConst(const SRef s, const char* name) {
    assert(strlen(name) != 0);
    PTRef ptr = PTRef_Undef;
    if (s == sort_BOOL) {
        if ((strcmp(name, tk_true) != 0) && (strcmp(name, tk_false) != 0)) {
            char *msg = (char*)malloc(strlen(e_bad_constant)+1);
            strcpy(msg, e_bad_constant);
            ptr = PTRef_Undef;
        }
        ptr = mkVar(s, name);
    } else {
        ptr = mkVar(s, name);
    }
    // Code to allow efficient constant detection.
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
    else {
        tr = insertTermHash(f, args);
        if (isUFTerm(tr) || isUP(tr)) {
            for (int i = 0; i < args.size(); i++) {
                if (hasSortBool(args[i])) {
                    setAppearsInUF(args[i]);
                    setAppearsInUF(mkNot(args[i]));
                }
            }
        }
    }
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
        if (isBooleanOperator(tr)) return false;
        else return true;
//        if (isDisequality(tr) && !isDistinct(tr)) return true;
//        if (isUP(tr)) return true;
    }
    return false;
}

SRef Logic::declareSort(const char* id, char** msg)
{
    if (containsSort(id))
        return getSortRef(id);

    IdRef idr = id_store.newIdentifier(id);
    vec<SRef> tmp;
    SRef sr = sort_store.newSort(idr, tmp);
    declare_sort_hook(sr);
    std::string sort_name{id};
    SRef rval = sort_store[sort_name.c_str()];
    ufsorts.insert(rval, true);
//    printf("Inserted sort %s\n", id);
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
    for (unsigned i = interpreted_functions.size(); i <= id; i++)
        interpreted_functions.push(false);
    interpreted_functions[id] = interpreted;
    return sr;
}

bool Logic::defineFun(const char* fname, const vec<PTRef>& args, SRef rsort, PTRef tr)
{
    if (defined_functions.has(fname))
        return false; // already there
    TFun tpl_fun(fname, args, rsort, tr);
    defined_functions.insert(fname, tpl_fun);
    // This part is a bit silly..
    Tterm tmp;
    defined_functions_vec.push(tmp);
    Tterm& t = defined_functions_vec.last();
    t.setName(tpl_fun.getName());
    t.setBody(tpl_fun.getBody());
    for (int i = 0; i < args.size(); i++)
        t.addArg(args[i]);
    return true;
}

vec<Tterm>& Logic::getFunctions()
{
    return defined_functions_vec;
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
    if(isIte(sym))
        return mkIte(terms);
    if(sym == getSym_implies())
        return mkImpl(terms);
    if(sym == getSym_true())
        return getTerm_true();
    if(sym == getSym_false())
        return getTerm_false();
    return mkFun(sym, terms);
}

PTRef
Logic::insertTermHash(SymRef sym, const vec<PTRef>& terms)
{
    PTRef res = PTRef_Undef;
    char *msg;
    if (terms.size() == 0) {
        if (term_store.hasCtermKey(sym)) //cterm_map.contains(sym))
            res = term_store.getFromCtermMap(sym); //cterm_map[sym];
        else {
            res = term_store.newTerm(sym, terms);
            term_store.addToCtermMap(sym, res); //cterm_map.insert(sym, res);
        }
    }
    else if (!isBooleanOperator(sym)) {
        if (!sym_store[sym].left_assoc() &&
            !sym_store[sym].right_assoc() &&
            !sym_store[sym].chainable() &&
            !sym_store[sym].pairwise() &&
            sym_store[sym].nargs() != terms.size_())
        {
            msg = (char*)malloc(strlen(e_argnum_mismatch)+1);
            strcpy(msg, e_argnum_mismatch);
            return PTRef_Undef;
        }
        PTLKey k;
        k.sym = sym;
        terms.copyTo(k.args);
        if (sym_store[sym].commutes()) {
            termSort(k.args);
        }
        if (term_store.hasCplxKey(k))
            res = term_store.getFromCplxMap(k);
        else {
            res = term_store.newTerm(sym, k.args);
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
    return isUF(getSymRef(ptr));
}

bool
Logic::isIF(SymRef sref) const
{
    return getSym(sref).nargs() > 0 && interpreted_functions[getSym(sref).getId()];
}

bool Logic::isIF(PTRef ptr) const {
    return isIF(getSymRef(ptr));
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
    if (sym_store[getPterm(ptr).symb()].isInterpreted()) return false;

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
    termSort(args);
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
bool Logic::varsubstitute(PTRef root, const Map<PTRef, PtAsgn, PTRefHash> & substs, PTRef & tr_new)
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
                args_mapped.capacity(t.size());
#ifdef SIMPLIFY_DEBUG
                printf("Arg substitution found for %s:\n", printTerm(tr));
#endif
                bool changed = false;
                for (int i = 0; i < t.size(); i++) {
                    PTRef sub = gen_sub[t[i]];
                    changed |= (sub != t[i]);
                    args_mapped.push(sub);
#ifdef SIMPLIFY_DEBUG
                    printf("  %s -> %s\n", printTerm(t[i]), printTerm(gen_sub[t[i]]));
#endif
                }
                char* msg;
                result = changed ? insertTerm(t.symb(), args_mapped, &msg) : tr;
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
            uint32_t id = Idx(getPterm(keys[i]).getId());
            while (id >= seen.size())
                seen.push(undef);
            seen[id] = white;
        }
        vec<SubstNode*> roots;
        for (int i = 0; i < keys.size(); i++) {
            uint32_t id = Idx(getPterm(keys[i]).getId());
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
                    if (seen[Idx(getPterm(var_tr).getId())] == white) {
                        seen[Idx(getPterm(var_tr).getId())] = black;
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
                    } else if (seen[Idx(getPterm(var_tr).getId())] == black) {
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
            TarjanAlgorithm tarjan;
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
            if (seen[Idx(getPterm(roots[i]->tr).getId())] != white)
                continue;
            vec<SubstNode*> queue;
            queue.push(roots[i]);
            while (queue.size() > 0) {
                SubstNode* n = queue.last(); queue.pop();
                if (seen[Idx(getPterm(n->tr).getId())] != white)
                    continue;
                seen[Idx(getPterm(n->tr).getId())] = black;
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
lbool Logic::retrieveSubstitutions(const vec<PtAsgn>& facts, Map<PTRef,PtAsgn,PTRefHash>& substs)
{
    for (int i = 0; i < facts.size(); i++) {
        PTRef tr = facts[i].tr;
        lbool sgn = facts[i].sgn;
        // Join equalities
        if (isEquality(tr) && sgn == l_True) {
#ifdef SIMPLIFY_DEBUG
            cerr << "Identified an equality: " << printTerm(tr) << endl;
#endif
            const Pterm& t = getPterm(tr);
            // n will be the reference
            if (isUFEquality(tr) || isIff(tr)) {
                // This is the simple replacement to elimiate enode terms where possible
                assert(t.size() == 2);
                // One of them should be a var
                const Pterm& a1 = getPterm(t[0]);
                const Pterm& a2 = getPterm(t[1]);
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
                    if (substs.has(var)) {
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
                if (substs[tr].tr==getTerm_true() || substs[tr].tr==getTerm_false()) {
                    if (term != substs[tr].tr) {
                        return l_False;
                    }
                }
            } else substs.insert(tr, PtAsgn(term, l_True));
        }
    }
    breakSubstLoops(substs);
    return l_Undef;
}

lbool Logic::isInHashes(vec<Map<PTRef,lbool,PTRefHash>*>& hashes, Map<PTRef,lbool,PTRefHash>& curr_hash, PtAsgn pta)
{
    PTRef tr = pta.tr;
    lbool asgn = l_Undef;
    for (int i = 0; i < hashes.size(); i++) {
        Map<PTRef,lbool,PTRefHash>& h = *(hashes[i]);
        if (h.has(tr)) {
            asgn = h[tr];
            break;
        }
    }
    if (asgn == l_Undef) {
        if (curr_hash.has(tr))
            asgn = curr_hash[tr];
    }
    if (asgn == l_Undef)
        return l_Undef;
    if (asgn != pta.sgn)
        return l_False;
    else if (asgn == pta.sgn)
        return l_True;
    assert(false);
    throw std::logic_error("Unreachable code!");
}

//
// TODO: Also this should most likely be dependent on the theory being
// used.  Depending on the theory a fact should either be added on the
// top level or left out to reduce e.g. simplex matrix size.
//
void Logic::getNewFacts(PTRef root, vec<Map<PTRef,lbool,PTRefHash>*>& prev_units, Map<PTRef,lbool,PTRefHash>& facts)
{
    Map<PtAsgn,bool,PtAsgnHash> isdup;
    vec<PtAsgn> queue;
    PTRef p;
    lbool sign;
    purify(root, p, sign);
    queue.push(PtAsgn(p, sign));

    while (queue.size() != 0) {
        PtAsgn pta = queue.last(); queue.pop();

        if (isdup.has(pta)) continue;
        isdup.insert(pta, true);

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
        else {
            lbool prev_val = isInHashes(prev_units, facts, pta);
            if (prev_val != l_Undef && prev_val != pta.sgn)
                return; // conflict
            else if (prev_val == pta.sgn)
                continue; // Already seen

            assert(prev_val == l_Undef);
            if (isEquality(pta.tr) and pta.sgn == l_True) {
                facts.insert(pta.tr, pta.sgn);
            }
            else if (isUP(pta.tr) and pta.sgn == l_True) {
                facts.insert(pta.tr, pta.sgn);
            }
            else if (isXor(pta.tr) and pta.sgn == l_True) {
                Pterm& t = getPterm(pta.tr);
                facts.insert(mkEq(t[0], mkNot(t[1])), l_True);
            }
            else {
                PTRef c;
                lbool c_sign;
                purify(pta.tr, c, c_sign);
                if (isBoolAtom(c)) {
                    facts.insert(c, c_sign^(pta.sgn == l_False));
                }
            }
        }
    }

#ifdef SIMPLIFY_DEBUG
    cerr << "True facts" << endl;
    vec<Map<PTRef,lbool,PTRefHash>::Pair> facts_dbg;
    facts.getKeysAndVals(facts_dbg);
    for (int i = 0; i < facts_dbg.size(); i++)
        cerr << (facts_dbg[i].data == l_True ? "" : "not ") << printTerm(facts_dbg[i].key) << " (" << facts_dbg[i].key.x << ")" << endl;
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
        return getTerm_true();
}

void
Logic::dumpChecksatToFile(ostream& dump_out)
{
    dump_out << "(check-sat)" << endl;
#ifdef PRODUCE_PROOF
    dump_out << "(get-interpolants)" << endl;
#endif
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
    for (int i = 0; i < symbols.size(); ++i)
    {
        SymRef s = symbols[i];
        if (s == getSym_true() || s == getSym_false() || s == getSym_anon())
            continue;
        if (isConstant(s)) {
            if (isBuiltinConstant(s)) continue;
            dump_out << "(declare-const ";
        }
        //else if (!isUF(s) && !isVar(s)) continue;
        else if (isBuiltinFunction(s)) continue;
        else {
            dump_out << "(declare-fun ";
        }
        char* sym = printSym(s);
        dump_out << sym << " ";
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
        sprintf( buf, "?def%d", Idx(getPterm(e).getId()) );

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
Logic::dumpFunction(ostream& dump_out, const TFun& tpl_fun)
{
    PTRef tr_function = tpl_fun.getBody();
    Pterm& t = getPterm(tr_function);
    const char* name = tpl_fun.getName();
    char *quoted_name = protectName(name);

    dump_out << "(define-fun " << quoted_name << " ( ";
    free(quoted_name);
    const vec<PTRef>& args = tpl_fun.getArgs();
    for (int i = 0; i < args.size(); ++i) {
        char* arg_name = printTerm(args[i]);
        const char* sort_name = getSortName(getSortRef(args[i]));
        dump_out << '(' << arg_name << ' ' <<  sort_name << ") ";
        free(arg_name);
    }
    const char* rsort = getSortName(tpl_fun.getRetSort());
    dump_out << ") " << rsort;
    dumpFormulaToFile(dump_out, tpl_fun.getBody(), false, false);
    dump_out << ')' << endl;
}

PTRef
Logic::instantiateFunctionTemplate(const char* fname, Map<PTRef, PTRef,PTRefHash>& subst)
{
    const TFun& tpl_fun = defined_functions[fname];
    PTRef tr = tpl_fun.getBody();
    Pterm& t = getPterm(tpl_fun.getBody());
    const vec<PTRef>& args = tpl_fun.getArgs();
    Map<PTRef,PtAsgn,PTRefHash> substs_asgn;
    for (int i = 0; i < args.size(); i++) {
        if (!subst.has(args[i]))
            return PTRef_Undef;
        PTRef subst_target_tr = subst[args[i]];
        if (getSortRef(subst_target_tr) != getSortRef(args[i]))
            return PTRef_Undef;
        PtAsgn subst_target = {subst_target_tr, l_True};
        substs_asgn.insert(args[i], subst_target);
    }
    PTRef tr_subst;
    varsubstitute(tr, substs_asgn, tr_subst);
    if (getSortRef(tr_subst) != tpl_fun.getRetSort()) {
        printf("Error: the function return sort changed in instantiation from %s to %s\n", getSortName(tpl_fun.getRetSort()), getSortName(getSortRef(tr_subst)));
        return PTRef_Undef;
    }

    return tr_subst;
}


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
    int pid = fork();
    if(pid == -1){
        std::cerr << "Failed to fork\n";
        // consider throwing and exception
        return false;
    }
    else if( pid == 0){
        // child process
        execlp( config.certifying_solver, config.certifying_solver, implies, NULL );
        perror( "Child process error: " );
        exit( 1 );
    }
    else{
        // parent
        int status;
        waitpid(pid, &status, 0);
        switch ( WEXITSTATUS( status ) )
        {
            case 0:
//                std::cerr << "Implication holds!\n";
                tool_res = false;
                break;
            case 1:
//                std::cerr << "Implication does not hold!\n";
//                std::cerr << "Antecedent: " << logic.printTerm(implicant) << '\n';
//                std::cerr << "Consequent: " << logic.printTerm(implicated) << '\n';
                tool_res = true;
                break;
            default:
                perror( "Parent process error" );
                exit( EXIT_FAILURE );
        }
    }

    return !tool_res;
}

void Logic::conjoinItes(PTRef root, PTRef& new_root)
{
    vec<PTRef> queue;
    Map<PTRef,bool,PTRefHash> seen;
    queue.push(root);
    vec<PTRef> args;
    while (queue.size() != 0) {
        PTRef el = queue.last();
        queue.pop();
        if (seen.has(el)) continue;
        if (isVar(el) && isIteVar(el)) {
            PTRef ite = getTopLevelIte(el);
            args.push(ite);
            queue.push(ite);
        }
        for (int i = 0; i < getPterm(el).size(); i++)
            queue.push(getPterm(el)[i]);
        seen.insert(el, true);
    }
    args.push(root);
    new_root = mkAnd(args);
#ifdef PRODUCE_PROOF
    addIPartitions(new_root, getIPartitions(root));
#endif
}

#ifdef PRODUCE_PROOF

void Logic::propagatePartitionMask(PTRef root) {
    ipartitions_t& p = getIPartitions(root);
    Map<PTRef, bool, PTRefHash> seen;
    std::vector<PTRef> queue {root};

    while (!queue.empty()) {
        PTRef current = queue.back();
        queue.pop_back();
        if (!seen.has(current)) {
            const Pterm& c_term = this->getPterm(current);
            for (int j = 0; j < c_term.size(); ++j) {
                addIPartitions(c_term[j], p);
                queue.push_back(c_term[j]);
            }
            if (isUF(current) || isUP(current)) {
                addIPartitions(c_term.symb(), p);
            }
            seen.insert(current, false);
        }
    }
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
    auto parts = logic.getPartitions();
    vec<PTRef> a_args;
    for(auto part : parts)
    {
        const auto & p_mask = logic.getIPartitions(part);
        if(isAlocal(p_mask, mask)) {
            a_args.push(part);
        }
        else if(!isBlocal(p_mask, mask)) {
            opensmt_error("Assertion is neither A or B");
        }
    }
    // add ites:
    vec<Map<PTRef,Ite,PTRefHash,Equal<PTRef>>::Pair> entries;
    top_level_ites.getKeysAndVals(entries);
    for (int i = 0; i < entries.size(); ++i) {
        if(isAlocal(getIPartitions(entries[i].key), mask)){
            a_args.push(entries[i].data.repr);
        }
    }
    PTRef A = logic.mkAnd(a_args);

    return A;
}

PTRef
Logic::getPartitionB(const ipartitions_t& mask)
{
    Logic& logic = *this;
    auto parts = logic.getPartitions();
    vec<PTRef> b_args;
    for(auto part : parts)
    {
        const auto & p_mask = logic.getIPartitions(part);
        if(isBlocal(p_mask, mask)) {
            b_args.push(part);
        }
        else if(!isAlocal(p_mask, mask)) {
            opensmt_error("Assertion is neither A or B");
        }
    }
    // add ites:
    vec<Map<PTRef,Ite,PTRefHash,Equal<PTRef>>::Pair> entries;
    top_level_ites.getKeysAndVals(entries);
    for (int i = 0; i < entries.size(); ++i) {
        if(isBlocal(getIPartitions(entries[i].key), mask)){
            b_args.push(entries[i].data.repr);
        }
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
#endif

void
Logic::collectStats(PTRef root, int& n_of_conn, int& n_of_eq, int& n_of_uf, int& n_of_if)
{
    set<PTRef> seen_terms;
    queue<PTRef> to_visit;
    n_of_conn = n_of_eq = n_of_uf = n_of_if = 0;
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
        else if(isIF(node))
        {
            ++n_of_if;
            Pterm& pnode = getPterm(node);
            for(int i = 0; i < pnode.size(); ++i)
                to_visit.push(pnode[i]);
        }
    }
}

bool Logic::isIteVar(PTRef tr) const { return top_level_ites.has(tr); }
PTRef Logic::getTopLevelIte(PTRef tr) { return top_level_ites[tr].repr; }
void Logic::conjoinExtras(PTRef root, PTRef& new_root) { conjoinItes(root, new_root); }

IdRef       Logic::newIdentifier (const char* name)            { return id_store.newIdentifier(name); }
IdRef       Logic::newIdentifier (const char* name, vec<int>& nl){ return id_store.newIdentifier(name, nl); }
// Fetching sorts
bool        Logic::containsSort  (const char* name)      const { return sort_store.containsSort(name); }

SRef        Logic::newSort       (IdRef idr, const char* name, vec<SRef>& tmp) { return sort_store.newSort(idr, name, tmp); }

SRef        Logic::getSortRef    (const char* name)      const { return sort_store[name]; }
SRef        Logic::getSortRef    (const PTRef tr)        const { return getSortRef(getPterm(tr).symb()); }
SRef        Logic::getSortRef    (const SymRef sr)       const { return getSym(sr).rsort(); }
Sort*       Logic::getSort       (const SRef s)                { return sort_store[s]; }
const char* Logic::getSortName   (const SRef s)                { return sort_store.getName(s); }


PTRef       Logic::mkAnd         (PTRef a1, PTRef a2) { vec<PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkAnd(tmp); }
PTRef      Logic::mkAnd         (const std::vector<PTRef> & v) { vec<PTRef> tmp; for(PTRef ref : v) {tmp.push(ref);} return mkAnd(tmp); }

PTRef      Logic::mkOr          (PTRef a1, PTRef a2) { vec<PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkOr(tmp); }
PTRef      Logic::mkOr          (const std::vector<PTRef> & v) { vec<PTRef> tmp; for(PTRef ref : v) {tmp.push(ref);} return mkOr(tmp); }

PTRef       Logic::mkXor         (PTRef a1, PTRef a2) { vec <PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkXor(tmp); }

PTRef       Logic::mkIte         (PTRef c, PTRef t, PTRef e) { vec<PTRef> tmp; tmp.push(c); tmp.push(t); tmp.push(e); return mkIte(tmp); }


PTRef       Logic::mkEq          (PTRef a1, PTRef a2) { vec<PTRef> v; v.push(a1); v.push(a2); return mkEq(v); }
void Logic::dumpFunctions(ostream& dump_out) { vec<const char*> names; defined_functions.getKeys(names); for (int i = 0; i < names.size(); i++) dumpFunction(dump_out, names[i]); }
void Logic::dumpFunction(ostream& dump_out, const char* tpl_name) { if (defined_functions.has(tpl_name)) dumpFunction(dump_out, defined_functions[tpl_name]); else printf("; Error: function %s is not defined\n", tpl_name); }
void Logic::dumpFunction(ostream& dump_out, const std::string s) { dumpFunction(dump_out, s.c_str()); }

void Logic::dumpFunction(ostream& dump_out, const Tterm& t) { dumpFunction(dump_out, TFun(t, getSortRef(t.getBody()))); }

// The Boolean connectives
SymRef        Logic::getSym_true      ()              const { return sym_TRUE;     }
SymRef        Logic::getSym_false     ()              const { return sym_FALSE;    }
SymRef        Logic::getSym_and       ()              const { return sym_AND;      }
SymRef        Logic::getSym_or        ()              const { return sym_OR;       }
SymRef        Logic::getSym_xor       ()              const { return sym_XOR;      }
SymRef       Logic::getSym_not       ()              const { return sym_NOT;      }
SymRef       Logic::getSym_eq        ()              const { return sym_EQ;       }
SymRef       Logic::getSym_ite       ()              const { return sym_ITE;      }
SymRef       Logic::getSym_implies   ()              const { return sym_IMPLIES;  }
SymRef       Logic::getSym_distinct  ()              const { return sym_DISTINCT; }
SRef         Logic::getSort_bool     ()              const { return sort_BOOL;    }

PTRef         Logic::getTerm_true     ()              const { return term_TRUE;  }
PTRef         Logic::getTerm_false    ()              const { return term_FALSE; }

bool          Logic::isEquality       (SymRef tr)     const { return equalities.has(tr);    }
bool          Logic::isEquality       (PTRef tr)      const { return equalities.has(term_store[tr].symb());}
bool          Logic::isUFEquality     (PTRef tr)      const { return isEquality(tr) && !hasSortBool(getPterm(tr)[0]); }
bool          Logic::isTheoryEquality (PTRef tr)      const { return isUFEquality(tr); }
bool          Logic::isDisequality    (SymRef tr)     const { return disequalities.has(tr); }
bool          Logic::isDisequality    (PTRef tr)      const { return disequalities.has(term_store[tr].symb()); }
bool          Logic::isIte            (SymRef tr)     const { return ites.has(tr);          }
bool          Logic::isIte            (PTRef tr)      const { return ites.has(term_store[tr].symb()); }

bool         Logic::isBooleanOperator  (PTRef tr)        const { return isBooleanOperator(term_store[tr].symb()); }
bool         Logic::isBuiltinSort      (const SRef sr)   const { return sr == sort_BOOL; }
bool         Logic::isBuiltinConstant  (const SymRef sr) const { return isConstant(sr) && (sr == sym_TRUE || sr == sym_FALSE); }
bool         Logic::isBuiltinConstant  (const PTRef tr)  const { return isBuiltinConstant(getPterm(tr).symb()); }
bool         Logic::Logic::isConstant         (PTRef tr)        const { return isConstant(getPterm(tr).symb()); }
bool         Logic::isUFTerm           (PTRef tr)        const { return isUFSort(getSortRef(tr)); }
bool         Logic::isUFSort           (const SRef sr)   const { return ufsorts.has(sr); }


bool        Logic::isVar              (SymRef sr)     const { return sym_store[sr].nargs() == 0 && !isConstant(sr); }
bool        Logic::isVar              (PTRef tr)      const { return isVar(getPterm(tr).symb()); }

bool        Logic::isBoolAtom         (PTRef tr)      const { return hasSortBool(tr) && isVar(tr); }


bool        Logic::isAnd(PTRef tr)  const { return getPterm(tr).symb() == getSym_and(); }
bool        Logic::isAnd(SymRef sr) const { return sr == getSym_and(); }
bool        Logic::isOr (PTRef tr)  const { return getPterm(tr).symb() == getSym_or (); }
bool        Logic::isOr (SymRef sr) const { return sr == getSym_or(); }
bool        Logic::isNot(PTRef tr)  const { return getPterm(tr).symb() == getSym_not(); }
bool        Logic::isNot(SymRef sr) const { return sr == getSym_not(); }
bool        Logic::isXor(SymRef sr) const { return sr == getSym_xor(); }
bool        Logic::isXor(PTRef tr)  const { return isXor(getPterm(tr).symb()); }
bool        Logic::isImplies(SymRef sr) const { return sr == getSym_implies(); }
bool        Logic::isImplies(PTRef tr)  const { return isImplies(getPterm(tr).symb()); }
bool        Logic::isTrue(SymRef sr) const { return sr == getSym_true(); }
bool        Logic::isTrue(PTRef tr)  const { return isTrue(getPterm(tr).symb()); }
bool        Logic::isFalse(SymRef sr) const { return sr == getSym_false(); }
bool        Logic::isFalse(PTRef tr)  const { return isFalse(getPterm(tr).symb()); }
bool        Logic::isDistinct(SymRef sr) const { return sr == getSym_distinct(); }
bool        Logic::isDistinct(PTRef tr) const { return isDistinct(getPterm(tr).symb()); }
bool        Logic::isIff(SymRef sr) const { return sr == getSym_eq(); }
bool        Logic::isIff(PTRef tr) const { return isIff(getPterm(tr).symb()); }


bool        Logic::hasSortBool(PTRef tr) const { return sym_store[getPterm(tr).symb()].rsort() == sort_BOOL; }
bool        Logic::hasSortBool(SymRef sr) const { return sym_store[sr].rsort() == sort_BOOL; }

inline bool Logic::isPredef           (string&)        const { return false; };

char* Logic::printTerm        (PTRef tr)                 const { return printTerm_(tr, false, false); }
char* Logic::printTerm        (PTRef tr, bool l, bool s) const { return printTerm_(tr, l, s); }

void Logic::termSort(vec<PTRef>& v) const { sort(v, LessThan_PTRef()); }

void  Logic::purify     (PTRef r, PTRef& p, lbool& sgn) const {p = r; sgn = l_True; while (isNot(p)) { sgn = sgn^1; p = getPterm(p)[0]; }}

inline int     Logic::verbose                       ( ) const { return config.verbosity(); }