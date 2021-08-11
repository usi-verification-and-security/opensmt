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
#include "SubstLoopBreaker.h"
#include "OsmtApiException.h"
#include "Substitutor.h"

#include <queue>
#include <set>

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
const char* Logic::s_abstract_value_prefix = "@";

std::size_t Logic::abstractValueCount = 0;

// The constructor initiates the base logic (Boolean)
Logic::Logic() :
      distinctClassCount(0)
    , sort_store(id_store)
    , term_store(sym_store)
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
    , use_extended_signature(false)
    , subst_num(0)
{
    char* msg;
    // We can't use declareSort here since it assumes that sort_BOOL
    // exists for making the equality symbol!
    IdRef bool_id = id_store.newIdentifier("Bool");
    vec<SRef> tmp_srefs;
    sort_store.newSort(bool_id, tmp_srefs);
    sort_BOOL = sort_store["Bool"];

    term_TRUE = mkConst(getSort_bool(), tk_true);
    if (term_TRUE == PTRef_Undef) {
        printf("Error in constructing term %s\n", tk_true);
        assert(false);
    }
    sym_TRUE = sym_store.nameToRef(tk_true)[0];
    sym_store[sym_TRUE].setNoScoping();
    sym_store.setInterpreted(sym_TRUE);

    term_FALSE = mkConst(getSort_bool(), tk_false);
    if (term_FALSE  == PTRef_Undef) {
        printf("Error in constructing term %s\n", tk_false);
        assert(false);
    }
    sym_FALSE = sym_store.nameToRef(tk_false)[0];
    sym_store[sym_FALSE].setNoScoping();
    sym_store.setInterpreted(sym_FALSE);

    // The anonymous symbol for the enodes of non-propositional Ites and propositional formulas nested inside UFs (or UPs)
    vec<SRef> params;
    sym_ANON = sym_store.newSymb(tk_anon, params);

    params.push(sort_BOOL);

    // UF not that is not visible outside the uf solver
    sym_UF_NOT = sym_store.newSymb(tk_uf_not, params);


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

    // Boolean distincts will never be created (they are turned to a Boolean expression),
    // but we need this symbol so that they can be processed.
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
    sortToIte.insert(sort_BOOL, sym_ITE);

    /////////////////////////////////////////
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
        if (isKnownToUser(sr)) {
            ss << name_escaped;
        } else {
            ss << "(as " << name_escaped << " " << getSortName(getSortRef(sr)) << ")";
        }
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
    if ((sr == sym_EQ) && not appearsInUF(ptr)) {
        assert(p.nargs() == 2);
        return false;
    }
    else if (hasSortBool(sr) && appearsInUF(ptr)) {
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

void Logic::unsetAppearsInUF(PTRef tr) {
    tr = isNot(tr) ? getPterm(tr)[0]: tr;
    uint32_t id = Idx(getPterm(tr).getId());
    appears_in_uf[id] = UFAppearanceStatus::removed;
}

void Logic::setAppearsInUF(PTRef tr) {
    assert(not isNot(tr));
    int id = static_cast<int>(Idx(getPterm(tr).getId()));
    if (appears_in_uf.size() <= id || appears_in_uf[id] == UFAppearanceStatus::unseen) {
        propFormulasAppearingInUF.push(tr);
    }

    while (id >= appears_in_uf.size()) {
        appears_in_uf.push(UFAppearanceStatus::unseen);
    }

    appears_in_uf[id] = UFAppearanceStatus::appears;
}

bool Logic::appearsInUF(PTRef tr) const {
    tr = isNot(tr) ? getPterm(tr)[0] : tr;

    uint32_t id = Idx(getPterm(tr).getId());
    if (id < static_cast<unsigned int>(appears_in_uf.size()))
        return appears_in_uf[id] == UFAppearanceStatus::appears;
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
    sortToIte.insert(sr, tr);

    std::stringstream ss;
    ss << Logic::s_abstract_value_prefix << 'd' << sort_store.numSorts();
    defaultValueForSort.insert(sr, mkConst(sr, ss.str().c_str()));
    return true;
}

// The vec argument might be sorted!
PTRef Logic::resolveTerm(const char* s, vec<PTRef>& args, char** msg) {
    SymRef sref = term_store.lookupSymbol(s, args);
    if (sref == SymRef_Undef) {
        if (defined_functions.has(s)) {
            // Make a new function by substituting the arguments of defined_functions[s] with whatever is in args
            const vec<PTRef>& tpl_args = defined_functions[s].getArgs();
            SubstMap subst_map;
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

    rval = insertTerm(sref, args);
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
Logic::getDefaultValuePTRef(const SRef sref) const {
    if (sref == sort_BOOL) { return term_TRUE; }
    else {
        return defaultValueForSort[sref];

    }
}

PTRef
Logic::mkIte(const vec<PTRef>& args)
{
    if (!hasSortBool(args[0])) return PTRef_Undef;
    if (args.size() != 3) throw OsmtApiException("ITE needs to have 3 arguments");

    assert(args.size() == 3);
    if (isTrue(args[0]))    return args[1];
    if (isFalse(args[0]))   return args[2];
    if (args[1] == args[2]) return args[1];

    SRef sr = getSortRef(args[1]);
    if (sr != getSortRef(args[2])) {
        throw OsmtApiException("ITE arguments need to have same return sorts");
    }

    assert(sortToIte.has(sr));
    SymRef iteSym = sortToIte[sr];
    return mkFun(iteSym, args);

}

// Check if arguments contain trues or a false and return the simplified
// term
PTRef Logic::mkAnd(const vec<PTRef>& args) {
    if (args.size() == 0) { return getTerm_true(); }
    // Remove duplicates
    vec<PtAsgn> tmp_args;
    tmp_args.capacity(args.size());
    for (int i = 0; i < args.size(); i++) {
        if (!hasSortBool(args[i])) {
            return PTRef_Undef;
        }
        if (isNot(args[i])) {
            tmp_args.push(PtAsgn(getPterm(args[i])[0], l_False));
        } else {
            tmp_args.push(PtAsgn(args[i], l_True));
        }
    }
    std::sort(tmp_args.begin(), tmp_args.end(), LessThan_PtAsgn());
    int i, j;
    PtAsgn p = PtAsgn_Undef;
    for (i = 0, j = 0; i < tmp_args.size(); i++) {
        if (isFalse(tmp_args[i].tr)) {
            assert(tmp_args[i].sgn == l_True);
            return getTerm_false();
        } else if (isTrue(tmp_args[i].tr)) { // skip
            assert(tmp_args[i].sgn == l_True);
        } else if (p == tmp_args[i]) { // skip
        } else if (p.tr == tmp_args[i].tr && p.sgn != tmp_args[i].sgn) {
            return getTerm_false();
        } else {
            tmp_args[j++] = p = tmp_args[i];
        }
    }
    tmp_args.shrink(i - j);
    if (tmp_args.size() == 0) {
        return getTerm_true();
    } else if (tmp_args.size() == 1) {
        return tmp_args[0].sgn == l_True ? tmp_args[0].tr : mkNot(tmp_args[0].tr);
    }
    vec<PTRef> newargs;
    newargs.capacity(tmp_args.size());
    for (int k = 0; k < tmp_args.size(); k++) {
        newargs.push(tmp_args[k].sgn == l_True ? tmp_args[k].tr : mkNot(tmp_args[k].tr));
    }
    return mkFun(getSym_and(), newargs);
}

PTRef Logic::mkOr(const vec<PTRef>& args) {
    if (args.size() == 0) { return getTerm_false(); }
    // Remove duplicates
    vec<PtAsgn> tmp_args;
    tmp_args.capacity(args.size());
    for (int i = 0; i < args.size(); i++) {
        if (!hasSortBool(args[i])) {
            return PTRef_Undef;
        }
        if (isNot(args[i])) {
            tmp_args.push(PtAsgn(getPterm(args[i])[0], l_False));
        } else {
            tmp_args.push(PtAsgn(args[i], l_True));
        }
    }
    std::sort(tmp_args.begin(), tmp_args.end(), LessThan_PtAsgn());
    int i, j;
    PtAsgn p = PtAsgn_Undef;
    for (i = 0, j = 0; i < tmp_args.size(); i++) {
        if (isTrue(tmp_args[i].tr)) {
            assert(tmp_args[i].sgn == l_True);
            return getTerm_true();
        } else if (isFalse(tmp_args[i].tr)) { // skip
            assert(tmp_args[i].sgn == l_True);
        } else if (p == tmp_args[i]) { // skip
        } else if (p.tr == tmp_args[i].tr && p.sgn != tmp_args[i].sgn) {
            return getTerm_true();
        } else {
            tmp_args[j++] = p = tmp_args[i];
        }
    }
    tmp_args.shrink(i - j);
    if (tmp_args.size() == 0) {
        return getTerm_false();
    } else if (tmp_args.size() == 1) {
        return tmp_args[0].sgn == l_True ? tmp_args[0].tr : mkNot(tmp_args[0].tr);
    }
    vec<PTRef> newargs;
    newargs.capacity(tmp_args.size());
    for (int k = 0; k < tmp_args.size(); k++) {
        newargs.push(tmp_args[k].sgn == l_True ? tmp_args[k].tr : mkNot(tmp_args[k].tr));
    }
    return mkFun(getSym_or(), newargs);
}

PTRef Logic::mkXor(const vec<PTRef>& args) {
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

PTRef Logic::mkImpl(const vec<PTRef>& args) {

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

PTRef Logic::mkEq(const vec<PTRef>& args) {
    if (args.size() < 2) { return PTRef_Undef; }
    if (args.size() > 2) { // split to chain of equalities with 2 arguments
        vec<PTRef> binaryEqualities;
        vec<PTRef> argPair;
        argPair.growTo(2, PTRef_Undef);
        for (int i = 0; i < args.size() - 1; ++i) {
            argPair[0] = args[i];
            argPair[1] = args[i + 1];
            binaryEqualities.push(mkEq(argPair));
        }
        return mkAnd(binaryEqualities);
    }
    assert(args.size() == 2);
    if (isConstant(args[0]) && isConstant(args[1]))
        return (args[0] == args[1]) ? getTerm_true() : getTerm_false();
    if (args[0] == args[1]) return getTerm_true();
    // Simplify more here now that the equals type is known
    if (hasSortBool(args[0])) {
        if (args[0] == mkNot(args[1])) return getTerm_false();
        if (args[0] == getTerm_true() || args[1] == getTerm_true())
            return args[0] == getTerm_true() ? args[1] : args[0];
        if (args[0] == getTerm_false() || args[1] == getTerm_false())
            return args[0] == getTerm_false() ? mkNot(args[1]) : mkNot(args[0]);
    }
    SymRef eq_sym = term_store.lookupSymbol(tk_equals, args);
    return mkFun(eq_sym, args);
}

// Given args = {a_1, ..., a_n}, distinct(args) holds iff
// for all a_i, a_j \in args s.t. i != j: a_i != a_j
// General distinctions are represented as separate terms until the distinction classes have been used up.
// After this, they are written explicitly as the O(n^2) expansion.
PTRef Logic::mkDistinct(vec<PTRef>& args) {
    if (args.size() == 0) return getTerm_true();
    if (args.size() == 1) return getTerm_true();
    if (args.size() == 2) return mkNot(mkEq(args));

    // The boolean distinctness over > 2 args is false
    if (hasSortBool(args[0])) {
        assert(args.size() > 2);
        return getTerm_false();
    }

    termSort(args);

    for (int i = 1, j = 0; i < args.size(); i++, j++) {
        if (args[j] == args[i]) {
            return getTerm_false();
        }
    }

    SymRef diseq_sym = term_store.lookupSymbol(tk_distinct, args);
    assert(!isBooleanOperator(diseq_sym));
    PTLKey key;
    key.sym = diseq_sym;
    args.copyTo(key.args);
    if (term_store.hasCplxKey(key)) {
        return term_store.getFromCplxMap(key);
    }
    else {
        if (distinctClassCount < maxDistinctClasses) {
            PTRef res = term_store.newTerm(diseq_sym, args);
            term_store.addToCplxMap(std::move(key), res);
            distinctClassCount++;
            return res;
        }
        else {
            vec<PTRef> distinct_terms;
            for (int i = 0; i < args.size(); i++) {
                for (int j = i + 1; j < args.size(); j++) {
                    vec<PTRef> small_distinct{args[i], args[j]};
                    distinct_terms.push(mkDistinct(small_distinct));
                }
            }
            return mkAnd(distinct_terms);
        }
    }
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
    SymRef sr = newSymb(name, sort_args);
    assert(sr != SymRef_Undef);
    if (sr == SymRef_Undef) {
        std::cerr << "Unexpected situation in  Logic::mkVar for " << name << std::endl;
        assert(symNameToRef(name).size() == 1);
        sr = symNameToRef(name)[0];
    }
    vec<PTRef> tmp;
    PTRef ptr = mkFun(sr, tmp);
    assert (ptr != PTRef_Undef);

    return ptr;
}

PTRef Logic::mkUniqueAbstractValue(SRef s) {
    std::string uniqueName = s_abstract_value_prefix + std::to_string(abstractValueCount++);
    return mkVar(s, uniqueName.c_str());
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
    markConstant(ptr);

    return ptr;
}

void Logic::markConstant(PTRef ptr) {
    SymId id = sym_store[getPterm(ptr).symb()].getId();
    markConstant(id);
}

void Logic::markConstant(SymId id) {
    // Code to allow efficient constant detection.
    while (id >= static_cast<unsigned int>(constants.size()))
        constants.push(false);
    constants[id] = true;
}

PTRef Logic::mkUninterpFun(SymRef f, const vec<PTRef> & args) {
    PTRef tr = mkFun(f, args);
    if (not isUFTerm(tr) and not isUP(tr)) {
        char * name = printSym(f);
        std::string msg = "Unknown symbol: " + std::string(name);
        free(name);
        throw OsmtApiException(msg);
    }
    return tr;
}

PTRef Logic::mkFun(SymRef f, const vec<PTRef>& args)
{
    PTRef tr;
    if (f == SymRef_Undef)
        tr = PTRef_Undef;
    else {
        tr = insertTermHash(f, args);
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
    PTRef tr = mkFun(sr, tmp2);
    return tr;
}

SRef Logic::declareSort(const char* id, char** msg)
{
    if (containsSort(id)) {
        return getSortRef(id);
    }

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
    SymRef sr = sym_store.newSymb(fname, comb_args);
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
    defined_functions.insert(fname, TemplateFunction(fname, args, rsort, tr));
    return true;
}

PTRef Logic::insertTerm(SymRef sym, vec<PTRef>& terms)
{
    if (sym == getSym_and())
        return mkAnd(terms);
    if (sym == getSym_or())
        return mkOr(terms);
    if (sym == getSym_xor())
        return mkXor(terms);
    if (sym == getSym_not())
        return mkNot(terms[0]);
    if (isEquality(sym))
        return mkEq(terms);
    if (isDisequality(sym))
        return mkDistinct(terms);
    if (isIte(sym))
        return mkIte(terms);
    if (sym == getSym_implies())
        return mkImpl(terms);
    if (sym == getSym_true())
        return getTerm_true();
    if (sym == getSym_false())
        return getTerm_false();
    if (isVar(sym)) {
        assert(terms.size() == 0);
        return mkFun(sym, terms);
    }
    return mkUninterpFun(sym, terms);
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
            term_store.addToCplxMap(std::move(k), res);
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
            term_store.addToBoolMap(std::move(k), res);
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

// A term is atom if its sort is Bool and
//  (i)   it is a variable or constant (number of arguments is 0)
//  (ii)  it is a non-boolean equality or distinct
//  (iii) it is a theory atom (here we check only UF atoms, logics should override this method to add their specific checks)
bool Logic::isAtom(PTRef r) const {
    const Pterm& t = term_store[r];
    if (sym_store[t.symb()].rsort() == getSort_bool()) {
        if (t.size() == 0) return true;
        if (t.symb() == getSym_not() ) return false;
        // At this point all arguments of equivalence have the same sort.  Check only the first
        if (isEquality(t.symb()) && (sym_store[term_store[t[0]].symb()].rsort() != getSort_bool())) return true;
        if (isDisequality(t.symb())) return true;
        if (isUP(r)) return true;
    }
    return false;
}

//
// The substitutions for the term riddance from osmt1
//
opensmt::pair<lbool,Logic::SubstMap> Logic::retrieveSubstitutions(const vec<PtAsgn>& facts)
{
    MapWithKeys<PTRef,PtAsgn,PTRefHash> substs;
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
                        return {l_False, SubstMap()};
                    }
                }
            } else {
                substs.insert(tr, PtAsgn(term, l_True));
            }
        }
    }
    SubstLoopBreaker slb(*this);
    return {l_Undef, slb(std::move(substs))};
}

void Logic::substitutionsTransitiveClosure(SubstMap & substs) {
    bool changed = true;
    const auto & keys = substs.getKeys(); // We can use direct pointers, since no elements are inserted or deleted in the loop
    std::vector<char> notChangedElems(substs.getSize(), 0); // True if not changed in last iteration, initially False
    while (changed) {
        changed = false;
        for (int i = 0; i < keys.size(); ++i) {
            if (notChangedElems[i]) { continue; }
            PTRef & val = substs[keys[i]];
            PTRef oldVal = val;
            PTRef newVal = Substitutor(*this, substs).rewrite(oldVal);
            if (oldVal != newVal) {
                changed = true;
                val = newVal;
            }
            else {
                notChangedElems[i] = 1;
            }
        }
    }
}

//
// TODO: Also this should most likely be dependent on the theory being
// used.  Depending on the theory a fact should either be added on the
// top level or left out to reduce e.g. simplex matrix size.
//
bool Logic::getNewFacts(PTRef root, MapWithKeys<PTRef, lbool, PTRefHash> & facts)
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

        Pterm const & t = getPterm(pta.tr);

        if (isAnd(pta.tr) and pta.sgn == l_True) {
            for (PTRef l : t) {
                PTRef c;
                lbool c_sign;
                purify(l, c, c_sign);
                queue.push(PtAsgn(c, c_sign));
            }
        } else if (isOr(pta.tr) and (pta.sgn == l_False)) {
            for (PTRef l : t) {
                PTRef c;
                lbool c_sign;
                purify(l, c, c_sign);
                queue.push(PtAsgn(c, c_sign ^ true));
            }
        } else {
            lbool prev_val = facts.has(pta.tr) ? facts[pta.tr] : l_Undef;
            if (prev_val != l_Undef && prev_val != pta.sgn)
                return false; // conflict
            else if (prev_val == pta.sgn)
                continue; // Already seen

            assert(prev_val == l_Undef);
            if (isEquality(pta.tr) and pta.sgn == l_True) {
                facts.insert(pta.tr, pta.sgn);
            } else if (isUP(pta.tr) and pta.sgn == l_True) {
                facts.insert(pta.tr, pta.sgn);
            } else if (isXor(pta.tr) and pta.sgn == l_True) {
                Pterm const & xorTerm = getPterm(pta.tr);
                facts.insert(mkEq(xorTerm[0], mkNot(xorTerm[1])), l_True);
            } else {
                PTRef c;
                lbool c_sign;
                purify(pta.tr, c, c_sign);
                if (isBoolAtom(c)) {
                    facts.insert(c, c_sign^(pta.sgn == l_False));
                }
            }
        }
    }
    return true;
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
Logic::dumpChecksatToFile(ostream& dump_out) const
{
    dump_out << "(check-sat)" << endl;
    dump_out << "(exit)" << endl;
}

void
Logic::dumpHeaderToFile(ostream& dump_out) const
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
        const Symbol& symb = sym_store[s];
        dump_out << "(";
        for(unsigned int j = 0; j < symb.nargs(); ++j)
        {
            dump_out << sort_store.getName(symb[j]) << " ";
        }
        dump_out << ") " << sort_store.getName(symb.rsort()) << ")" << endl;
    }
}

void
Logic::dumpFormulaToFile(ostream & dump_out, PTRef formula, bool negate, bool toassert) const
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
        const Pterm& term = getPterm(e);
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
    if (toassert)
        dump_out << ")" << endl;
}

void
Logic::dumpFunction(ostream& dump_out, const TemplateFunction& tpl_fun)
{
    const std::string& name = tpl_fun.getName();
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
Logic::instantiateFunctionTemplate(const char* fname, const SubstMap& subst)
{
    const TemplateFunction& tpl_fun = defined_functions[fname];
    PTRef tr = tpl_fun.getBody();
    const vec<PTRef>& args = tpl_fun.getArgs();
    for (int i = 0; i < args.size(); i++) {
        if (!subst.has(args[i])) {
            std::string argName = pp(args[i]);
            throw OsmtApiException(
                    "No value provided for function " + tpl_fun.getName() + " argument " + argName);
        }
        if (getSortRef(subst[args[i]]) != getSortRef(args[i])) {
            throw OsmtApiException("Substitution source and target sort mismatch" );
        }
    }

    PTRef tr_subst = Substitutor(*this, subst).rewrite(tr);
    assert (getSortRef(tr_subst) == tpl_fun.getRetSort());
    return tr_subst;
}

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


PTRef Logic::conjoinExtras(PTRef root) { return root; }

IdRef       Logic::newIdentifier (const char* name)            { return id_store.newIdentifier(name); }
IdRef       Logic::newIdentifier (const char* name, vec<int>& nl){ return id_store.newIdentifier(name, nl); }
// Fetching sorts
bool        Logic::containsSort  (const char* name)      const { return sort_store.containsSort(name); }

SRef        Logic::newSort       (IdRef idr, const char* name, vec<SRef>& tmp) { return sort_store.newSort(idr, name, tmp); }

SRef        Logic::getSortRef    (const char* name)      const { return sort_store[name]; }
SRef        Logic::getSortRef    (const PTRef tr)        const { return getSortRef(getPterm(tr).symb()); }
SRef        Logic::getSortRef    (const SymRef sr)       const { return getSym(sr).rsort(); }
Sort*       Logic::getSort       (const SRef s)                { return sort_store[s]; }
const char* Logic::getSortName   (const SRef s)          const { return sort_store.getName(s); }

void Logic::dumpFunctions(ostream& dump_out) { vec<const char*> names; defined_functions.getKeys(names); for (int i = 0; i < names.size(); i++) dumpFunction(dump_out, names[i]); }
void Logic::dumpFunction(ostream& dump_out, const char* tpl_name) { if (defined_functions.has(tpl_name)) dumpFunction(dump_out, defined_functions[tpl_name]); else printf("; Error: function %s is not defined\n", tpl_name); }
void Logic::dumpFunction(ostream& dump_out, const std::string s) { dumpFunction(dump_out, s.c_str()); }

// The Boolean connectives
SymRef        Logic::getSym_true      ()              const { return sym_TRUE;     }
SymRef        Logic::getSym_false     ()              const { return sym_FALSE;    }
SymRef        Logic::getSym_and       ()              const { return sym_AND;      }
SymRef        Logic::getSym_or        ()              const { return sym_OR;       }
SymRef        Logic::getSym_xor       ()              const { return sym_XOR;      }
SymRef        Logic::getSym_not       ()              const { return sym_NOT;      }
SymRef        Logic::getSym_eq        ()              const { return sym_EQ;       }
SymRef        Logic::getSym_ite       ()              const { return sym_ITE;      }
SymRef        Logic::getSym_implies   ()              const { return sym_IMPLIES;  }
SymRef        Logic::getSym_distinct  ()              const { return sym_DISTINCT; }
SRef          Logic::getSort_bool     ()              const { return sort_BOOL;    }

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
bool         Logic::isConstant         (PTRef tr)        const { return isConstant(getPterm(tr).symb()); }
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
bool        Logic::isIff(SymRef sr) const { return sr == getSym_eq(); }
bool        Logic::isIff(PTRef tr) const { return isIff(getPterm(tr).symb()); }


bool        Logic::hasSortBool(PTRef tr) const { return sym_store[getPterm(tr).symb()].rsort() == sort_BOOL; }
bool        Logic::hasSortBool(SymRef sr) const { return sym_store[sr].rsort() == sort_BOOL; }

inline bool Logic::isPredef           (string&)        const { return false; };

char* Logic::printTerm        (PTRef tr)                 const { return printTerm_(tr, false, false); }
char* Logic::printTerm        (PTRef tr, bool l, bool s) const { return printTerm_(tr, l, s); }

void Logic::termSort(vec<PTRef>& v) const { sort(v, LessThan_PTRef()); }

void  Logic::purify     (PTRef r, PTRef& p, lbool& sgn) const {p = r; sgn = l_True; while (isNot(p)) { sgn = sgn^1; p = getPterm(p)[0]; }}
