#include "sorts/SStore.h"
#include "sorts/Sort.h"
#include "terms/TStore.h"
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

// The constructor initiates the base logic (Boolean)
Logic::Logic(SMTConfig& c, SStore& s, TStore& t, PtStore& pt) :
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

    TRef tr;

    tr = sym_store.newTerm(tk_true, params);
    if (tr == TRef_Undef) { assert(false); }
    sym_store[tr].setNoScoping();
    sym_TRUE = tr;
    vec<PTRef> tmp;
    term_TRUE  = term_store.insertTerm(sym_TRUE,  tmp);

    tr = sym_store.newTerm(tk_false, params);
    if (tr == TRef_Undef) { assert(false); }
    sym_store[tr].setNoScoping();
    sym_FALSE = tr;
    term_FALSE = term_store.insertTerm(sym_FALSE, tmp);

    params.push(sort_store["Bool 0"]);
    tr = sym_store.newTerm(tk_not, params);
    if (tr == TRef_Undef) { assert(false); }
    sym_store[tr].setNoScoping();
    sym_NOT = tr;

    params.push(sort_store["Bool 0"]);

    tr = sym_store.newTerm(tk_equals, params);
    if (tr == TRef_Undef) { assert(false); }
    if (sym_store[tr].setRightAssoc() == false) { assert(false); } // TODO: Remove and clean
    sym_store[tr].setNoScoping();
    sym_EQ = tr;
    equalities.insert(sym_EQ, true);

    tr = sym_store.newTerm(tk_implies, params);
    if (tr == TRef_Undef) { assert(false); }
    if (sym_store[tr].setRightAssoc() == false) { assert(false); } // TODO: Remove and clean
    sym_store[tr].setNoScoping();
    sym_IMPLIES = tr;

    tr = sym_store.newTerm(tk_and, params);
    if (tr == TRef_Undef) { assert(false); }
    if (sym_store[tr].setLeftAssoc() == false) assert(false);
    sym_store[tr].setNoScoping();
    sym_AND = tr;

    tr = sym_store.newTerm(tk_or, params);
    if (tr == TRef_Undef) { assert(false); }
    if (sym_store[tr].setLeftAssoc() == false) assert(false);
    sym_store[tr].setNoScoping();
    sym_OR = tr;

    tr = sym_store.newTerm(tk_xor, params);
    if (tr == TRef_Undef) { assert(false); }
    if (sym_store[tr].setLeftAssoc() == false) assert(false);
    sym_store[tr].setNoScoping();
    sym_XOR = tr;
}

bool Logic::isTheorySymbol(TRef tr) const {
    Term& t = sym_store[tr];
    // Boolean var
    if (t.rsort() == sort_BOOL && t.nargs() == 0) return false;
    // Standard Boolean operators
    if (tr == sym_NOT) return false;
    if (tr == sym_EQ)  return false;
    if (tr == sym_IMPLIES) return false;
    if (tr == sym_AND) return false;
    if (tr == sym_OR)  return false;
    if (tr == sym_XOR) return false;
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

    TRef tr;

    tr = sym_store.newTerm(tk_equals, params);
    if (tr == TRef_Undef) { return false; }
    sym_store[tr].setNoScoping();
    equalities.insert(tr, true);

    // distinct
    tr = sym_store.newTerm(tk_distinct, params);
    if (tr == TRef_Undef) { return false; }
    if (sym_store[tr].setPairwise() == false) return false;
    sym_store[tr].setNoScoping();
    disequalities.insert(tr, true);

    // ite
    params.clear();
    params.push(sr);
    params.push(br);
    params.push(sr);
    params.push(sr);

    tr = sym_store.newTerm(tk_ite, params);
    if (tr == TRef_Undef) { return false; }
    sym_store[tr].setNoScoping();

    return true;
}


// Adds the uninterpreted predicate ptr if it is an uninterpreted predicate.
// Returns reference to corresponding equality term or PTRef_Undef.  Creates
// the eq term if it does not exist previously.
PTRef Logic::addUP(PTRef ptr) const {
    if (UP_map.contains(ptr)) return UP_map[ptr];
    Pterm& t = term_store[ptr];
    Term& sym = sym_store[t.symb()];
    if (sym.nargs() == 0) return PTRef_Undef; // This is a Boolean constant
    if (sym.rsort() != getSort_bool()) return PTRef_Undef;
    int i;
    for (i = 0; i < sym.size(); i++)
        if (sym[i] == getSort_bool()) break;
    if (i != sym.size()) return PTRef_Undef;
    // A new boolean predicate
    vec<PTRef> args;
    args.push(ptr);
    args.push(getTerm_true());
    return term_store.lookupTerm(tk_equals, args);
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


