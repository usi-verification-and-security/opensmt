#include "sorts/SStore.h"
#include "sorts/Sort.h"
#include "terms/TStore.h"
#include "Logic.h"

/***********************************************************
 * Class defining logic
 ***********************************************************/

// The constructor initiates the base logic (Boolean)
Logic::Logic(SMTConfig& c, SStore& s, TStore& t) :
      config(c)
    , sort_store(s)
    , term_store(t)
    , is_set(false)
{
    sort_store.insertStore(new Sort(*(new Identifier("Bool"))));
    sort_BOOL = sort_store["Bool 0"];

    vec<SRef> params;

    char* tk_true    = strdup("true");
    char* tk_false   = strdup("false");
    char* tk_not     = strdup("not");
    char* tk_equals  = strdup("=");
    char* tk_implies = strdup("=>");
    char* tk_and     = strdup("and");
    char* tk_or      = strdup("or");
    char* tk_xor     = strdup("xor");

    params.push(sort_store["Bool 0"]);

    TRef tr;

    tr = term_store.newTerm(tk_true, params);
    if (tr == TRef_Undef) { free(tk_true); assert(false); }
    term_store[tr].setNoScoping();
    sym_TRUE = tr;

    tr = term_store.newTerm(tk_false, params);
    if (tr == TRef_Undef) { free(tk_false); assert(false); }
    term_store[tr].setNoScoping();
    sym_FALSE = tr;

    params.push(sort_store["Bool 0"]);
    tr = term_store.newTerm(tk_not, params);
    if (tr == TRef_Undef) { free(tk_not); assert(false); }
    term_store[tr].setNoScoping();
    sym_NOT = tr;

    params.push(sort_store["Bool 0"]);

    tr = term_store.newTerm(tk_equals, params);
    if (tr == TRef_Undef) { free(tk_equals); assert(false); }
    if (term_store[tr].setRightAssoc() == false) { assert(false); } // TODO: Remove and clean
    term_store[tr].setNoScoping();
    sym_EQ = tr;

    tr = term_store.newTerm(tk_implies, params);
    if (tr == TRef_Undef) { free(tk_implies); assert(false); }
    if (term_store[tr].setRightAssoc() == false) { assert(false); } // TODO: Remove and clean
    term_store[tr].setNoScoping();

    tr = term_store.newTerm(tk_and, params);
    if (tr == TRef_Undef) { free(tk_and); assert(false); }
    if (term_store[tr].setLeftAssoc() == false) assert(false);
    term_store[tr].setNoScoping();
    sym_AND = tr;

    tr = term_store.newTerm(tk_or, params);
    if (tr == TRef_Undef) { free(tk_or); assert(false); }
    if (term_store[tr].setLeftAssoc() == false) assert(false);
    term_store[tr].setNoScoping();
    sym_OR = tr;

    tr = term_store.newTerm(tk_xor, params);
    if (tr == TRef_Undef) { free(tk_or); assert(false); }
    if (term_store[tr].setLeftAssoc() == false) assert(false);
    term_store[tr].setNoScoping();
    sym_XOR = tr;
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

    char* tk_equals   = strdup("=");
    char* tk_distinct = strdup("distinct");
    char* tk_ite      = strdup("ite");

    // Equality

    TRef tr;

    tr = term_store.newTerm(tk_equals, params);
    if (tr == TRef_Undef) { free(tk_equals); return false; }
    term_store[tr].setNoScoping();
    equalities.insert(tr, true);

    // distinct
    tr = term_store.newTerm(tk_distinct, params);
    if (tr == TRef_Undef) { free(tk_distinct); return false; }
    if (term_store[tr].setPairwise() == false) return false;
    term_store[tr].setNoScoping();
    disequalities.insert(tr, true);

    // ite
    params.clear();
    params.push(sr);
    params.push(br);
    params.push(sr);
    params.push(sr);

    tr = term_store.newTerm(tk_ite, params);
    if (tr == TRef_Undef) { free(tk_ite); return false; }
    term_store[tr].setNoScoping();

    return true;
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


