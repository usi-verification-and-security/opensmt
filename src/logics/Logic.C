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


#include "sorts/SStore.h"
#include "pterms/PtStore.h"
#include "Logic.h"
#include "common/TreeOps.h"
#include "minisat/mtl/Sort.h"

/***********************************************************
 * Class defining logic
 ***********************************************************/

const char* Logic::e_argnum_mismatch = "incorrect number of arguments";
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

// The constructor initiates the base logic (Boolean)
Logic::Logic(SMTConfig& c, IdentifierStore& i, SStore& s, SymStore& t, PtStore& pt) :
      config(c)
    , id_store(i)
    , sort_store(s)
    , sym_store(t)
    , term_store(pt)
    , is_set(false)
{
    IdRef bool_id = id_store.newIdentifier("Bool");
    vec<SRef> tmp_srefs;
    sort_store.newSort(bool_id, tmp_srefs);
    sort_BOOL = sort_store["Bool"];

    vec<SRef> params;

    params.push(sort_store["Bool"]);

    SymRef tr;

    const char* msg;
    tr = sym_store.newSymb(tk_true, params, &msg);
    if (tr == SymRef_Undef) { assert(false); }
    sym_store[tr].setNoScoping();
    sym_TRUE = tr;
    vec<PTRef> tmp;
    term_TRUE  = insertTerm(sym_TRUE,  tmp, &msg);
    assert(term_TRUE != PTRef_Undef);

    tr = sym_store.newSymb(tk_false, params, &msg);
    if (tr == SymRef_Undef) { assert(false); }
    sym_store[tr].setNoScoping();
    sym_FALSE = tr;
    term_FALSE = insertTerm(sym_FALSE, tmp, &msg);
    assert(term_FALSE != PTRef_Undef);

    params.push(sort_store["Bool"]);
    tr = sym_store.newSymb(tk_not, params, &msg);
    if (tr == SymRef_Undef) { assert(false); }
    sym_store[tr].setNoScoping();
    sym_NOT = tr;

    params.push(sort_store["Bool"]);

    tr = sym_store.newSymb(tk_equals, params, &msg);
    if (tr == SymRef_Undef) { assert(false); }
    if (sym_store[tr].setRightAssoc() == false) { assert(false); } // TODO: Remove and clean
    sym_store[tr].setNoScoping();
    sym_store[tr].setCommutes();
    sym_EQ = tr;
    equalities.insert(sym_EQ, true);

    tr = sym_store.newSymb(tk_implies, params, &msg);
    if (tr == SymRef_Undef) { assert(false); }
    if (sym_store[tr].setRightAssoc() == false) { assert(false); } // TODO: Remove and clean
    sym_store[tr].setNoScoping();
    sym_IMPLIES = tr;

    tr = sym_store.newSymb(tk_and, params, &msg);
    if (tr == SymRef_Undef) { assert(false); }
    if (sym_store[tr].setLeftAssoc() == false) assert(false);
    sym_store[tr].setNoScoping();
    sym_store[tr].setCommutes();
    sym_AND = tr;

    tr = sym_store.newSymb(tk_or, params, &msg);
    if (tr == SymRef_Undef) { assert(false); }
    if (sym_store[tr].setLeftAssoc() == false) assert(false);
    sym_store[tr].setNoScoping();
    sym_store[tr].setCommutes();
    sym_OR = tr;

    tr = sym_store.newSymb(tk_xor, params, &msg);
    if (tr == SymRef_Undef) { assert(false); }
    if (sym_store[tr].setLeftAssoc() == false) assert(false);
    sym_store[tr].setCommutes();
    sym_store[tr].setNoScoping();
    sym_XOR = tr;

    tr = sym_store.newSymb(tk_distinct, params, &msg);
    if (tr == SymRef_Undef) { assert(false); }
    if (sym_store[tr].setPairwise() == false) assert(false);
    sym_store[tr].setNoScoping();
    sym_store[tr].setCommutes();
    sym_DISTINCT = tr;

    params.push(sort_store["Bool"]);
    tr = sym_store.newSymb(tk_ite, params, &msg);
    if (tr == SymRef_Undef) { assert(false); }
    sym_store[tr].setNoScoping();
    sym_ITE = tr;
    ites.insert(tr, true);
}

bool Logic::isTheoryTerm(PTRef ptr) const {
    Pterm& p = term_store[ptr];
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
    Symbol& t = sym_store[tr];
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

bool Logic::setLogic(const char* l) {
    if (strcmp(l, "QF_UF") == 0) {
        config.logic                    = QF_UF;
//        config.sat_restart_first        = 100;
//        config.sat_restart_inc          = 1.5;

        is_set = true;
        name = "QF_UF";
        return true;
    }
    else return false;
}

// description: Add equality for each new sort
// precondition: sort has been declared
bool Logic::declare_sort_hook(SRef sr) {
    vec<SRef> params;

    SRef br = sort_store["Bool"];

    params.push(br);
    params.push(sr);
    params.push(sr);

    // Equality

    SymRef tr;

    const char* msg;
    tr = sym_store.newSymb(tk_equals, params, &msg);
    if (tr == SymRef_Undef) { return false; }
    sym_store[tr].setNoScoping();
    sym_store[tr].setCommutes();
    equalities.insert(tr, true);

    // distinct
    tr = sym_store.newSymb(tk_distinct, params, &msg);
    if (tr == SymRef_Undef) { return false; }
    if (sym_store[tr].setPairwise() == false) return false;
    sym_store[tr].setNoScoping();
    sym_store[tr].setCommutes();
    disequalities.insert(tr, true);

    // ite
    params.clear();
    params.push(sr);
    params.push(br);
    params.push(sr);
    params.push(sr);

    tr = sym_store.newSymb(tk_ite, params, &msg);
    if (tr == SymRef_Undef) { return false; }
    sym_store[tr].setNoScoping();
    ites.insert(tr, true);

    return true;
}

//
// XXX Comments? This method is currently under development
//
lbool Logic::simplifyTree(PTRef tr)
{
    vec<pi> queue;
    Map<PTRef,bool,PTRefHash> processed;
    queue.push(pi(tr));
    lbool last_val = l_Undef;
    while (queue.size() != 0) {
        // First find a node with all children processed.
        int i = queue.size()-1;
        if (processed.contains(queue[i].x)) {
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
                if (!processed.contains(cr)) {
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
        // (1) Check if my children (potentially simplified now) exist in
        //     term store and if so, replace them with the term store
        //     representative
        // (2) Simplify in place
        // (3) See if the simplifications resulted in me changing, and if so,
        //     look up from the table whether I'm already listed somewhere and add
        //     a mapping to the canonical representative, or create a new entry for
        //     me in the map.
        Pterm& t = getPterm(queue[i].x);
        // (1)
#ifdef SIMPLIFY_DEBUG
        if (t.size() > 0)
            cerr << "Now looking into the children of " << queue[i].x.x << endl;
        else
            cerr << "The node " << queue[i].x.x << " has no children" << endl;
#endif
        for (int e = 0; e < t.size(); e++) {
            PTRef cr = t[e];
#ifdef SIMPLIFY_DEBUG
            cerr << "child n. " << e << " is " << cr.x << endl;
#endif
            assert(cr != queue[i].x);
            Pterm& c = getPterm(cr);
            PTLKey k;
            k.sym = c.symb();
            for (int j = 0; j < c.size(); j++)
                k.args.push(c[j]);
            if (!isBooleanOperator(k.sym)) {
                assert(term_store.hasCplxKey(k));
#ifdef SIMPLIFY_DEBUG
                cerr << cr.x << " is not a boolean operator ";
                cerr << "and it maps to " << term_store.getFromCplxMap(k).x;
#endif
                t[e] = term_store.getFromCplxMap(k);
                assert(t[e] != queue[i].x);
            } else {
                assert(term_store.hasBoolKey(k)); //assert(term_store.bool_map.contains(k));
#ifdef SIMPLIFY_DEBUG
                cerr << cr.x << " is a boolean operator"
                     << " and it maps to " << term_store.bool_map[k].x << endl;
#endif
                t[e] = term_store.getFromBoolMap(k); //term_store.bool_map[k];
                assert(t[e] != queue[i].x);
            }
        }
#ifdef SIMPLIFY_DEBUG
        cerr << "After processing the children ended up with node " << term_store.printTerm(queue[i].x, true) << endl;
#endif
        // (2) Simplify in place
        PTRef orig = queue[i].x; // We need to save the original type in case the term gets simplified
        simplify(queue[i].x);
#ifdef SIMPLIFY_DEBUG
        cerr << "-> which was now simplified to " << term_store.printTerm(queue[i].x, true) << endl;
//      I don't seem to remember why this should be true or false?
//        if (orig != queue[i].x) {
//            assert(isTrue(queue[i].x) || isFalse(queue[i].x));
//            assert(isAnd(orig) || isOr(orig) || isEquality(orig) || isNot(orig));
//        }
#endif
        processed.insert(orig, true);
        // Make sure my key is in term hash
#ifdef SIMPLIFY_DEBUG
        cerr << "Making sure " << orig.x << " is in term_store hash" << endl;
        cerr << "Pushing symb " << t.symb().x << " to hash key" << endl;
#endif
        PTLKey k;
        k.sym = t.symb();
        for (int j = 0; j < t.size(); j++) {
#ifdef SIMPLIFY_DEBUG
            cerr << "Pushing arg " << t[j].x << " to hash key" << endl;
#endif
            k.args.push(t[j]);
        }
        if (!isBooleanOperator(k.sym)) {
            if (!term_store.hasCplxKey(k)) {
                term_store.addToCplxMap(k, queue[i].x);
#ifdef SIMPLIFY_DEBUG
                cerr << "sym " << k.sym.x << " args <";
                for (int j = 0; j < k.args.size(); j++) {
                    cerr << k.args[j].x << " ";
                }
                cerr << "> maps to " << term_store.getFromCplxMap(k).x << endl;
#endif
            }
            PTRef l = term_store.getFromCplxMap(k);
            // This is being kept on record in case the root term gets simplified
            if (isTrue(l)) last_val = l_True;
            else if (isFalse(l)) last_val = l_False;
            else last_val = l_Undef;
        } else {
            if (!term_store.hasBoolKey(k)) {//bool_map.contains(k)) {
                term_store.addToBoolMap(k, queue[i].x); //bool_map.insert(k, queue[i].x);
#ifdef SIMPLIFY_DEBUG
                cerr << "sym " << k.sym.x << " args ";
                for (int j = 0; j < k.args.size(); j++) {
                    cerr << k.args[j].x << " ";
                }
                cerr << "maps to " << term_store.bool_map[k].x << endl;
#endif
            }
            PTRef l = term_store.getFromBoolMap(k); //bool_map[k];
            // This is being kept on record in case the root term gets simplified
            if (isTrue(l)) last_val = l_True;
            else if (isFalse(l)) last_val = l_False;
            else last_val = l_Undef;
        }
        queue.pop();
    }
    return last_val;
}

// The vec argument might be sorted!
PTRef Logic::resolveTerm(const char* s, vec<PTRef>& args, char** msg) {
    SymRef sref = term_store.lookupSymbol(s, args);
    if (sref == SymRef_Undef) {
        asprintf(msg, "Unknown symbol %s", s);
        return PTRef_Undef;
    }
    assert(sref != SymRef_Undef);
    simplify(sref, args);
    PTRef rval;
    const char** msg2 = NULL;
    if (sref == SymRef_Undef)
        rval = PTRef_Undef;
    else
        rval = insertTerm(sref, args, msg2);
    if (msg2 != NULL)
        asprintf(msg, "%s", *msg2);
    return rval;
}

//
// Wrapper for simplify.  After running this, the reference should be checked
// for other occurrences since simplification might result in duplicate terms.
//
// In order to avoid duplicate appearances of terms making solving after
// cnfization slow a simplifyTree should be called to the subtree after calling
// the method.
//
void Logic::simplify(PTRef& tr) {
    Pterm& t = getPterm(tr);
    vec<PTRef> args;
    for (int i = 0; i < t.size(); i++)
        args.push(t[i]);
    SymRef sr = t.symb();
    SymRef sr_prev = sr;
    simplify(sr, args);

    const char** msg;

    // The if statement is not strictly speaking necessary, since checking for
    // duplicates needs to be performed anyway after this step
    if (sr != sr_prev && sr == getSym_true())
        tr = getTerm_true();
    else if (sr != sr_prev && sr == getSym_false())
        tr = getTerm_false();
    else
        tr = insertTerm(sr, args, msg);
}

//
// Sort a term if it commutes.
// The following simplifications implemented
// (should be refactored to separate methods?):
//  - `and':
//    - drop constant true terms
//    - convert an empty `and' to the constant term `true'
//    - convert an `and' containing `false' to a replicate `false'
//  - `or':
//    - drop constant false terms
//    - convert an empty `or' to a replicate `false' term
//    - convert an `or' containing `true' to a replicate `true'
//
//
void Logic::simplify(SymRef& s, vec<PTRef>& args) {
    // First sort it
#ifdef SORT_BOOLEANS
    if (sym_store[s].commutes())
#else
    if (sym_store[s].commutes() && !isAnd(s) && !isOr(s))
#endif
        sort(args, LessThan_PTRef());

    if (!isBooleanOperator(s) && !isEquality(s)) return;

    int dropped_args = 0;
    bool replace = false;
    if (s == getSym_and()) {
        int i, j;
        PTRef p = PTRef_Undef;
        for (i = j = 0; i < args.size(); i++) {
            if (args[i] == getTerm_false()) {
                args.clear();
                s = getSym_false();
#ifdef SIMPLIFY_DEBUG
                cerr << "and  -> false" << endl;
#endif
                return;
            } else if (args[i] != getTerm_true() && args[i] != p) {
                args[j++] = p = args[i];
            } else {
#ifdef SIMPLIFY_DEBUG
                cerr << "and -> drop" << endl;
#endif
            }
        }
        dropped_args = i-j;
        if (dropped_args == args.size()) {
            s = getSym_true();
            args.clear();
#ifdef SIMPLIFY_DEBUG
            cerr << "and -> true" << endl;
#endif
            return;
        } else if (dropped_args == args.size() - 1)
            replace = true;
        else if (dropped_args > 0)
            args.shrink(dropped_args);
    }
    if (s == getSym_or()) {
        int i, j;
        PTRef p = PTRef_Undef;
        for (i = j = 0; i < args.size(); i++) {
            if (args[i] == getTerm_true()) {
                args.clear();
                s = getSym_true();
#ifdef SIMPLIFY_DEBUG
                cerr << "or -> true" << endl;
#endif
                return;
            } else if (args[i] != getTerm_false() && args[i] != p) {
                args[j++] = p = args[i];
            } else {
#ifdef SIMPLIFY_DEBUG
                cerr << "or -> drop" << endl;
#endif
            }
        }
        dropped_args = i-j;
        if (dropped_args == args.size()) {
            s = getSym_false();
            args.clear();
#ifdef SIMPLIFY_DEBUG
            cerr << "or -> false" << endl;
#endif
            return;
        }
        else if (dropped_args == args.size() - 1)
            replace = true;
        else if (dropped_args > 0)
            args.shrink(dropped_args);
    }
    if (isEquality(s)) {
        assert(args.size() == 2);
        if (isBooleanOperator(s) && (args[0] == getTerm_true())) {
            Pterm& t = getPterm(args[1]);
            s = t.symb();
            args.clear();
            for (int i = 0; i < t.size(); i++)
                args.push(t[i]);
#ifdef SIMPLIFY_DEBUG
            cerr << "eq -> second" << endl;
#endif
            return;
        } else if (isBooleanOperator(s) && (args[0] == getTerm_false())) {
            PTRef old = args[1];
            PTRef tr = mkNot(args[1]);
            Pterm& t = getPterm(tr);
            s = t.symb();
            args.clear();
            args.push(old);
#ifdef SIMPLIFY_DEBUG
            cerr << "eq -> not second" << endl;
#endif
            return;
        } else if (isBooleanOperator(s) && (args[1] == getTerm_true())) {
            args.clear();
            Pterm& t = getPterm(args[0]);
            s = t.symb();
            args.clear();
            for (int i = 0; i < t.size(); i++)
                args.push(t[i]);
#ifdef SIMPLIFY_DEBUG
            cerr << "eq -> first" << endl;
#endif
            return;
        } else if (isBooleanOperator(s) && (args[1] == getTerm_false())) {
            PTRef old = args[0];
            PTRef tr = mkNot(args[0]);
            Pterm& t = getPterm(tr);
            s = t.symb();
            args.clear();
            args.push(old);
#ifdef SIMPLIFY_DEBUG
            cerr << "eq -> not first"<< endl;
#endif
            return;
        } else if (args[0] == args[1]) {
            args.clear();
            s = getSym_true();
#ifdef SIMPLIFY_DEBUG
            cerr << "eq -> true" << endl;
#endif
            return;
        } else if (isBooleanOperator(s) && (args[0] == mkNot(args[1]))) {
            args.clear();
            s = getSym_false();
#ifdef SIMPLIFY_DEBUG
            cerr << "eq -> false" << endl;
#endif
            return;
        }
    }
    if (isNot(s)) {
        if (isTrue(args[0])) {
            args.clear();
            s = getSym_false();
#ifdef SIMPLIFY_DEBUG
            cerr << "not -> false" << endl;
#endif
            return;
        }
        if (isFalse(args[0])) {
            args.clear();
            s = getSym_true();
#ifdef SIMPLIFY_DEBUG
            cerr << "not -> true" << endl;
#endif
            return;
        }
    }
    // Others, to be implemented:
    // - distinct
    // - implies
    // - xor
    // - ite
    if (replace) {
        // Return whatever is the sole argument
        Pterm& t = getPterm(args[0]);
        s = t.symb();
        args.clear();
        for (int i = 0; i < t.size(); i++)
            args.push(t[i]);
#ifdef SIMPLIFY_DEBUG
        cerr << " replace" << endl;
#endif
    }
}

// Check if arguments contain trues or a false and return the simplified
// term
PTRef Logic::mkAnd(vec<PTRef>& args) {
    char** msg;
    return resolveTerm(tk_and, args, msg);
}

PTRef Logic::mkOr(vec<PTRef>& args) {
    char** msg;
    return resolveTerm(tk_or, args, msg);
}


PTRef Logic::mkImpl(vec<PTRef>& args) {
    char** msg;
    return resolveTerm(tk_implies, args, msg);
}

PTRef Logic::mkEq(vec<PTRef>& args) {
    char** msg;
    return resolveTerm(tk_equals, args, msg);
}

PTRef Logic::mkNot(PTRef arg) {
    char** msg;
    vec<PTRef> tmp;
    tmp.push(arg);
    return resolveTerm(tk_not, tmp, msg);
}

PTRef Logic::mkConst(SRef s, const char* name) {
    vec<SRef> sort_args;
    sort_args.push(s);
    const char* msg;
    SymRef sr = newSymb(name, sort_args, &msg);
    if (sr == SymRef_Undef) {
        cerr << "Warning: while mkConst " << name << ": " << msg << endl;
        assert(symNameToRef(name).size() == 1);
        sr = symNameToRef(name)[0];
    }
    vec<PTRef> tmp;
    PTRef ptr = insertTerm(sr, tmp, &msg);
    assert (ptr != PTRef_Undef);
    return ptr;
}

PTRef Logic::mkFun(SymRef f, vec<PTRef>& args, const char** msg)
{
    return insertTerm(f, args, msg);
}

// A term is literal if its sort is Bool and
//  (i)   number of arguments is 0
//  (ii)  its symbol is sym_NOT and argument is a literal (nested nots
//        create literals?)
//  (iii) it is an atom stating an equivalence of non-boolean terms (terms must be purified at this point)
bool Logic::isLit(PTRef tr) const
{
    Pterm& t = getPterm(tr);
    if (sym_store[t.symb()].rsort() == getSort_bool()) {
        if (t.size() == 0) return true;
        if (t.symb() == getSym_not() ) return isLit(t[0]);
        // At this point all arguments of equivalence have the same sort.  Check only the first
        if (isEquality(tr) && (sym_store[getPterm(t[0]).symb()].rsort() != getSort_bool())) return true;
        if (isUP(tr)) return true;
    }
    return false;
}

SRef Logic::declareSort(const char* id, const char** msg)
{
    IdRef idr = id_store.newIdentifier(id);
    vec<SRef> tmp;
    SRef sr = sort_store.newSort(idr, tmp);
    declare_sort_hook(sr);
    char* sort_name;
    asprintf(&sort_name, "%s", id);
    return sort_store[sort_name];
}

SymRef Logic::declareFun(const char* fname, const SRef rsort, const vec<SRef>& args, const char** msg)
{
    vec<SRef> comb_args;

    assert(rsort != SRef_Undef);

    comb_args.push(rsort);

    for (int i = 0; i < args.size(); i++) {
        assert(args[i] != SRef_Undef);
        comb_args.push(args[i]);
    }
    return sym_store.newSymb(fname, comb_args, msg);
}

//
// Clone the deep term structure maintaining isomorphic reference structrue
//
PTRef Logic::cloneTerm(const PTRef& tr) {
    Map<PTRef,PTRef,PTRefHash > oldToNew;
    vec<PtChild> terms;
    getTermList(tr, terms, *this);
    PTRef ptr_new;
    for (int i = 0; i < terms.size(); i++) {
        PTRef ptr = terms[i].tr;
        if (oldToNew.contains(ptr)) continue;
        Pterm& pt = getPterm(ptr);
        vec<PTRef> args_new;
        for (int j = 0; j < pt.size(); j++)
            args_new.push(oldToNew[pt[j]]);
        ptr_new = term_store.newTerm(pt.symb(), args_new);
        oldToNew.insert(ptr, ptr_new);
    }
    return ptr_new;
}

PTRef Logic::insertTerm(SymRef sym, vec<PTRef>& terms, const char** msg) {
    PTRef res;
    if (terms.size() == 0) {
        if (term_store.hasCtermKey(sym)) //cterm_map.contains(sym))
            res = term_store.getFromCtermMap(sym); //cterm_map[sym];
        else {
            res = term_store.pta.alloc(sym, terms);
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
            *msg = e_argnum_mismatch;
            return PTRef_Undef;
        }
        PTLKey k;
        k.sym = sym;
        terms.copyTo(k.args);
        if (term_store.hasCplxKey(k))
            res = term_store.getFromCplxMap(k);
        else {
            res = term_store.pta.alloc(sym, terms);
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
            res = term_store.pta.alloc(sym, terms);
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

// Uninterpreted predicate p : U U* -> Bool
bool Logic::isUP(PTRef ptr) const {
    Pterm& t = term_store[ptr];
    SymRef sr = t.symb();
    // Should this really be an uninterpreted predicate?
    // At least it falsely identifies (= true false) as an uninterpreted
    // predicate without the extra condition
    if (isEquality(sr) || isDisequality(sr)) {
        if (isBooleanOperator(sr)) return false;
        else return true;
    }
    Symbol& sym = sym_store[sr];
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
    return false;
}

bool Logic::isAtom(PTRef r) const {
    Pterm& t = term_store[r];
    if (sym_store[t.symb()].rsort() == getSort_bool()) {
        if (t.size() == 0) return true;
        if (t.symb() == getSym_not() ) return false;
        // At this point all arguments of equivalence have the same sort.  Check only the first
        if (isEquality(t.symb()) && (sym_store[term_store[t[0]].symb()].rsort() != getSort_bool())) return true;
        if (isUP(r)) return true;
    }
    return false;
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
        if (equalities.contains(symbols[i]))
            equalities_sz ++;
        if (disequalities.contains(symbols[i]))
            disequalities_sz ++;
        if (ites.contains(symbols[i]))
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
        if (equalities.contains(symbols[i]))
            logicdata_buf[equalities_p ++] = symbols[i].x;
        if (disequalities.contains(symbols[i]))
            logicdata_buf[disequalities_p ++] = symbols[i].x;
        if (ites.contains(symbols[i]))
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
        if (!equalities.contains(sr))
            equalities.insert(sr, true);
    }

    int diseqs_sz = diseqs_buf[0];
    for (int i = 0; i < diseqs_sz - 1; i++) {
        SymRef sr = {(uint32_t)diseqs_buf[i+1]};
        if (!disequalities.contains(sr))
            disequalities.insert(sr, true);
    }

    int ites_sz = ites_buf[0];
    for (int i = 0; i < ites_sz - 1; i++) {
        SymRef sr = {(uint32_t)ites_buf[i+1]};
        if (!ites.contains(sr))
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


