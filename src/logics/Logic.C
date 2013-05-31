#include "sorts/SStore.h"
#include "pterms/PtStore.h"
#include "Logic.h"

/***********************************************************
 * Class defining logic
 ***********************************************************/

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

    tr = sym_store.newSymb(tk_true, params);
    if (tr == SymRef_Undef) { assert(false); }
    sym_store[tr].setNoScoping();
    sym_TRUE = tr;
    vec<PTRef> tmp;
    term_TRUE  = insertTerm(sym_TRUE,  tmp);

    tr = sym_store.newSymb(tk_false, params);
    if (tr == SymRef_Undef) { assert(false); }
    sym_store[tr].setNoScoping();
    sym_FALSE = tr;
    term_FALSE = insertTerm(sym_FALSE, tmp);

    params.push(sort_store["Bool 0"]);
    tr = sym_store.newSymb(tk_not, params);
    if (tr == SymRef_Undef) { assert(false); }
    sym_store[tr].setNoScoping();
    sym_NOT = tr;

    params.push(sort_store["Bool 0"]);

    tr = sym_store.newSymb(tk_equals, params);
    if (tr == SymRef_Undef) { assert(false); }
    if (sym_store[tr].setRightAssoc() == false) { assert(false); } // TODO: Remove and clean
    sym_store[tr].setNoScoping();
    sym_EQ = tr;
    equalities.insert(sym_EQ, true);

    tr = sym_store.newSymb(tk_implies, params);
    if (tr == SymRef_Undef) { assert(false); }
    if (sym_store[tr].setRightAssoc() == false) { assert(false); } // TODO: Remove and clean
    sym_store[tr].setNoScoping();
    sym_IMPLIES = tr;

    tr = sym_store.newSymb(tk_and, params);
    if (tr == SymRef_Undef) { assert(false); }
    if (sym_store[tr].setLeftAssoc() == false) assert(false);
    sym_store[tr].setNoScoping();
    sym_AND = tr;

    tr = sym_store.newSymb(tk_or, params);
    if (tr == SymRef_Undef) { assert(false); }
    if (sym_store[tr].setLeftAssoc() == false) assert(false);
    sym_store[tr].setNoScoping();
    sym_OR = tr;

    tr = sym_store.newSymb(tk_xor, params);
    if (tr == SymRef_Undef) { assert(false); }
    if (sym_store[tr].setLeftAssoc() == false) assert(false);
    sym_store[tr].setNoScoping();
    sym_XOR = tr;

    tr = sym_store.newSymb(tk_distinct, params);
    if (tr == SymRef_Undef) { assert(false); }
    if (sym_store[tr].setPairwise() == false) assert(false);
    sym_store[tr].setNoScoping();
    sym_DISTINCT = tr;

    params.push(sort_store["Bool 0"]);
    tr = sym_store.newSymb(tk_ite, params);
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

    tr = sym_store.newSymb(tk_equals, params);
    if (tr == SymRef_Undef) { return false; }
    sym_store[tr].setNoScoping();
    sym_store[tr].setCommutes();
    equalities.insert(tr, true);

    // distinct
    tr = sym_store.newSymb(tk_distinct, params);
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

    tr = sym_store.newSymb(tk_ite, params);
    if (tr == SymRef_Undef) { return false; }
    sym_store[tr].setNoScoping();
    ites.insert(tr, true);

    return true;
}

// The vec argument might be sorted!
PTRef Logic::resolveTerm(const char* s, vec<PTRef>& args) {
    SymRef sref = term_store.lookupSymbol(s, args);
    PTRef rval;
    if (sref == SymRef_Undef)
        rval = PTRef_Undef;
    else
        rval = insertTerm(sref, args);
    return rval;
}

PTRef Logic::mkAnd(vec<PTRef>& args) {
    return resolveTerm(tk_and, args);
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
    SymRef sr = newSymb(name, sort_args);
    if (sr == SymRef_Undef) {
        assert(symNameToRef(name).size() == 1);
        sr = symNameToRef(name)[0];
    }
    vec<PTRef> tmp;
    PTRef ptr = insertTerm(sr, tmp);
    assert (ptr != PTRef_Undef);
    return ptr;
}

PTRef Logic::insertTerm(SymRef sym, vec<PTRef>& terms) {
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
            sort(terms);
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
        res = term_store.pta.alloc(sym, terms);
    }
    return res;
}

// Uninterpreted predicate p : U U* -> Bool
bool Logic::isUP(PTRef ptr) const {
    Pterm& t = term_store[ptr];
    SymRef sr = t.symb();
    if (isEquality(sr) || isDisequality(sr)) return true;
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


