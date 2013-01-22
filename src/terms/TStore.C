#include "string.h"
#include "TStore.h"
#include "Term.h"

TRef TStore::newTerm(const char* fname, const vec<SRef>& args, bool, bool, bool, bool) {
    // Check if there already is a term called fname with same number of arguments of the same sort
    bool newterm = !contains(fname);
    if (newterm == false) {
        const vec<TRef>& trs = termTable[fname];
        for (int i = 0; i < trs.size(); i++) {
            if (ta[trs[i]].rsort() == args[0] && ta[trs[i]].nargs() == args.size_()-1) {
                uint32_t j;
                for (j = 0; j < ta[trs[i]].nargs(); j++) {
                    if (ta[trs[i]][j] != args[j+1])
                        break;
                }
                if (j == ta[trs[i]].nargs()) // The term exists already
                    return TRef_Undef;
            }
        }
    }

    TRef tr = ta.alloc(args, false);
    TId id = terms.size();
    terms.push(tr);

    trefToId.insert(tr, id);
    occList.push();                     // Get the occurrence list for this term
    if (newterm) {
        vec<TRef> trs;
        termTable.insert(fname, trs);
    }
    termTable[fname].push(tr);          // Map the name to term reference (why not id?), used in parsing
    char* tmp_name = strdup(fname);
    idToName.push(tmp_name);            // Map the id to name, used in error reporting
    ta[tr].id = id;                     // Tell the term its id, used in error reporting, and checking whether two terms could be equal in future?
    return tr;
}

//TRef TStore::insertStore(string name, vec<Sort*> args, Sort* rv) {
//    if (terms.contains(name))
//        return TRef_Undef;
//
//    TRef tr = terms.insert(Term_new(args, rv));
//    return tr;
//}
