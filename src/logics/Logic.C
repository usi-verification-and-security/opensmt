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

const char* Logic::s_sort_bool = "Bool 0";

// The constructor initiates the base logic (Boolean)
Logic::Logic(SMTConfig& c, SStore& s, SymStore& t, PtStore& pt) :
      config(c)
    , sort_store(s)
    , sym_store(t)
    , term_store(pt)
    , is_set(false)
{
    sort_store.insertStore(new Sort(*(new Identifier("Bool"))));
    sort_BOOL = sort_store["Bool 0"];

    vec<SRef> params;

    params.push(sort_store["Bool 0"]);

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

    params.push(sort_store["Bool 0"]);
    tr = sym_store.newSymb(tk_not, params, &msg);
    if (tr == SymRef_Undef) { assert(false); }
    sym_store[tr].setNoScoping();
    sym_NOT = tr;

    params.push(sort_store["Bool 0"]);

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

    params.push(sort_store["Bool 0"]);
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
        config.sat_restart_first        = 100;
        config.sat_restart_inc          = 1.5;

        is_set = true;
        name = "QF_UF";
        return true;
    }
    else return false;
}

// description: Add equality for each new sort
// precondition: sort has been declared
bool Logic::declare_sort_hook(Sort* s) {
    vec<SRef> params;

    SRef sr = sort_store[s->getCanonName()];
    SRef br = sort_store["Bool 0"];

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
// This method is currently under development
//
PTRef Logic::simplifyTree(PTRef tr)
{
    vec<pi> queue;
    Map<PTRef,bool,PTRefHash> processed;
    queue.push(pi(tr));
    while (queue.size() != 0) {
        int i = queue.size()-1;
        if (processed.contains(queue[i].x)) {
            queue.pop();
            continue;
        }
        bool unprocessed_children = false;
        if (queue[i].done == false) {
            cerr << "looking at term num " << queue[i].x.x << endl;
            Pterm& t = getPterm(queue[i].x);
            for (int j = 0; j < t.size(); j++) {
                PTRef cr = t[j];
                if (!processed.contains(cr)) {
                    unprocessed_children = true;
                    queue.push(pi(cr));
                    cerr << "pushing child " << cr.x << endl;
                }
            }
            queue[i].done = true;
        }
        if (unprocessed_children) continue;

        cerr << "Found a node " << queue[i].x.x << endl;
        cerr << "Before simplification it looks like " << term_store.printTerm(queue[i].x) << endl;
        // (1) Simplify in place
        // (2) Check if my children (potentially simplified now) exist in
        //     term store and if so, replace them with the term store
        //     representative
        // (3) If I am an `and' or an `or' and I only have a single child,
        //     replace myself with that term (in place)
        simplify(queue[i].x);
        cerr << "Simplified the node.  Result is " << term_store.printTerm(queue[i].x, true) << endl;
        Pterm& t = getPterm(queue[i].x);
        // (2)
        if (t.size() > 0)
            cerr << "Now looking into the children of " << queue[i].x.x << endl;
        else
            cerr << "The node " << queue[i].x.x << " has no children" << endl;
        for (int e = 0; e < t.size(); e++) {
            PTRef cr = t[e];
            cerr << "child n. " << e << " is " << cr.x << endl;
            assert(cr != queue[i].x);
            Pterm& c = getPterm(cr);
            PTLKey k;
            k.sym = c.symb();
            for (int j = 0; j < c.size(); j++)
                k.args.push(c[j]);
            if (!isBooleanOperator(k.sym)) {
                cerr << cr.x << " is not a boolean operator ";
                assert(term_store.cplx_map.contains(k));
                cerr << "and it maps to " << term_store.cplx_map[k].x << endl;
                t[e] = term_store.cplx_map[k];
                assert(t[e] != queue[i].x);
            } else {
                cerr << cr.x << " is a boolean operator";
                assert(term_store.bool_map.contains(k));
                cerr << " and it maps to " << term_store.bool_map[k].x << endl;
                t[e] = term_store.bool_map[k];
                assert(t[e] != queue[i].x);
                // (3)
                Pterm& c_canon = getPterm(t[e]);
                if (c_canon.size() == 1 && (isAnd(cr) || isOr(cr))) {
                    t[e] = c_canon[0];
                    assert(t[e] != queue[i].x);
                }
            }
        }
        cerr << "After processing the children ended up with node " << term_store.printTerm(queue[i].x, true) << endl;
        simplify(queue[i].x);
        cerr << "-> which was now simplified to " << term_store.printTerm(queue[i].x, true) << endl;
        processed.insert(queue[i].x, true);
        // Make sure my key is in term hash
        cerr << "Making sure " << queue[i].x.x << " is in term_store hash" << endl;
        PTLKey k;
        cerr << "Pushing symb " << t.symb().x << " to hash key" << endl;
        k.sym = t.symb();
        for (int j = 0; j < t.size(); j++) {
            cerr << "Pushing arg " << t[j].x << " to hash key" << endl;
            k.args.push(t[j]);
        }
        if (!isBooleanOperator(t.symb())) {
            if (!term_store.cplx_map.contains(k))
                term_store.cplx_map.insert(k, queue[i].x);
                cerr << "sym " << k.sym.x << " args ";
                for (int j = 0; j < k.args.size(); j++) {
                    cerr << k.args[j].x << " ";
                }
                cerr << "maps to " << term_store.cplx_map[k].x << endl;
        } else {
            if (!term_store.bool_map.contains(k)) {
                term_store.bool_map.insert(k, queue[i].x);
                cerr << "sym " << k.sym.x << " args ";
                for (int j = 0; j < k.args.size(); j++) {
                    cerr << k.args[j].x << " ";
                }
                cerr << "maps to " << term_store.bool_map[k].x << endl;
            }
        }
        queue.pop();
    }
}

// The vec argument might be sorted!
PTRef Logic::resolveTerm(const char* s, vec<PTRef>& args) {
    SymRef sref = term_store.lookupSymbol(s, args);
    assert(sref != SymRef_Undef);
    simplify(sref, args);
    PTRef rval;
    const char** msg;
    if (sref == SymRef_Undef)
        rval = PTRef_Undef;
    else
        rval = insertTerm(sref, args, msg);
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

    // The if statement is not strictly speaking necessary, since checking for
    // duplicates needs to be performed anyway after this step
    if (sr != sr_prev && sr == getSym_true())
        tr = getTerm_true();
    else if (sr != sr_prev && sr == getSym_false())
        tr = getTerm_false();
    else {
        t.sym = sr;
        for (int i = 0 ; i < args.size(); i++) {
            t[i] = args[i];
            t.shrink(t.size()-args.size());
        }
    }
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
    if (sym_store[s].commutes())
        sort(args, LessThan_PTRef());

    if (!isBooleanOperator(s)) return;

    int dropped_args = 0;
    bool replace = false;
    if (s == getSym_and()) {
        int i, j;
        PTRef p = PTRef_Undef;
        for (i = j = 0; i < args.size(); i++) {
            if (args[i] == getTerm_false()) {
                args.clear();
                s = getSym_false();
#ifdef PEDANTIC_DEBUG
                cerr << "and  -> false" << endl;
#endif
                return;
            } else if (args[i] != getTerm_true() && args[i] != p) {
                args[j++] = p = args[i];
            } else {
#ifdef PEDANTIC_DEBUG
                cerr << "and -> drop" << endl;
#endif
            }
        }
        dropped_args = i-j;
        if (dropped_args == args.size()) {
            s = getSym_true();
            args.clear();
#ifdef PEDANTIC_DEBUG
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
#ifdef PEDANTIC_DEBUG
                cerr << "or -> true" << endl;
#endif
                return;
            } else if (args[i] != getTerm_false() && args[i] != p) {
                args[j++] = p = args[i];
            } else {
#ifdef PEDANTIC_DEBUG
                cerr << "or -> drop" << endl;
#endif
            }
        }
        dropped_args = i-j;
        if (dropped_args == args.size()) {
            s = getSym_false();
            args.clear();
#ifdef PEDANTIC_DEBUG
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
        if (args[0] == getTerm_true()) {
            Pterm& t = getPterm(args[1]);
            s = t.symb();
            args.clear();
            for (int i = 0; i < t.size(); i++)
                args.push(t[i]);
#ifdef PEDANTIC_DEBUG
            cerr << "eq -> second" << endl;
#endif
            return;
        } else if (args[0] == getTerm_false()) {
            PTRef old = args[1];
            PTRef tr = mkNot(args[1]);
            Pterm& t = getPterm(tr);
            s = t.symb();
            args.clear();
            args.push(old);
#ifdef PEDANTIC_DEBUG
            cerr << "eq -> not second" << endl;
#endif
            return;
        } else if (args[1] == getTerm_true()) {
            args.clear();
            Pterm& t = getPterm(args[0]);
            s = t.symb();
            args.clear();
            for (int i = 0; i < t.size(); i++)
                args.push(t[i]);
#ifdef PEDANTIC_DEBUG
            cerr << "eq -> first" << endl;
#endif
            return;
        } else if (args[1] == getTerm_false()) {
            PTRef old = args[0];
            PTRef tr = mkNot(args[0]);
            Pterm& t = getPterm(tr);
            s = t.symb();
            args.clear();
            args.push(old);
#ifdef PEDANTIC_DEBUG
            cerr << "eq -> not first"<< endl;
#endif
            return;
        } else if (args[0] == args[1]) {
            args.clear();
            s = getSym_true();
#ifdef PEDANTIC_DEBUG
            cerr << "eq -> true" << endl;
#endif
            return;
        } else if (args[0] == mkNot(args[1])) {
            args.clear();
            s = getSym_false();
#ifdef PEDANTIC_DEBUG
            cerr << "eq -> false" << endl;
#endif
            return;
        }
    }
    // Others, to be implemented:
    // - distinct
    // - implies
    // - xor
    // - ite
    // - not
    if (replace) {
        // Return whatever is the sole argument
        Pterm& t = getPterm(args[0]);
        s = t.symb();
        args.clear();
        for (int i = 0; i < t.size(); i++)
            args.push(t[i]);
#ifdef PEDANTIC_DEBUG
        cerr << " replace" << endl;
#endif
    }
}

// Check if arguments contain trues or a false and return the simplified
// term
PTRef Logic::mkAnd(vec<PTRef>& args) {
        return resolveTerm(tk_and, args);
}

PTRef Logic::mkOr(vec<PTRef>& args) {
    return resolveTerm(tk_or, args);
}


PTRef Logic::mkImpl(vec<PTRef>& args) {
    return resolveTerm(tk_implies, args);
}

PTRef Logic::mkEq(vec<PTRef>& args) {
    return resolveTerm(tk_equals, args);
}

PTRef Logic::mkNot(PTRef arg) {
    vec<PTRef> tmp;
    tmp.push(arg);
    return resolveTerm(tk_not, tmp);
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
    Identifier i(id);
    Sort s(i);
    sort_store.insertStore(&s);
    declare_sort_hook(&s);
    char* sort_name;
    asprintf(&sort_name, "%s 0", id);
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
        if (term_store.cterm_map.contains(sym))
            res = term_store.cterm_map[sym];
        else {
            res = term_store.pta.alloc(sym, terms);
            term_store.cterm_map.insert(sym, res);
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
        if (term_store.cplx_map.contains(k))
            res = term_store.cplx_map[k];
        else {
            res = term_store.pta.alloc(sym, terms);
            term_store.cplx_map.insert(k, res);
        }
    }
    else {
        // Boolean operator
        PTLKey k;
        k.sym = sym;
        terms.copyTo(k.args);
        if (term_store.bool_map.contains(k)) {
            res = term_store.bool_map[k];
#ifdef PEDANTIC_DEBUG
            char* ts = printTerm(res);
//            cerr << "duplicate: " << ts << endl;
            ::free(ts);
#endif
        }
        else {
            res = term_store.pta.alloc(sym, terms);
            term_store.bool_map.insert(k, res);
#ifdef PEDANTIC_DEBUG
            char* ts = printTerm(res);
//            cerr << "new: " << ts << endl;
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
    if (UP_map.contains(ptr)) return UP_map[ptr];
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
    if (term_store.cplx_map.contains(k))
        return term_store.cplx_map[k];
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


