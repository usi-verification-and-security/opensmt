/*********************************************************************
Author: Antti Hyvarinen <antti.hyarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                          2008 - 2012 Roberto Bruttomesso


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

#include "Egraph.h"

class SimpSMTSolver;

// Choose debugging level
#define CHECK_INVARIANTS                            1
#define CHECK_INVARIANT_FORBID_LIST_SYMMERTRY       0
#define CHECK_INVARIANT_SIGNATURE_TABLE_CORRECTNESS 1

#define CHECK_EXPLANATIONS                          0

//=============================================================================
// Printing Routines


char* Egraph::printEqClass(PTRef tr) const {
    char* out;
    char* old;

    const ERef er = enode_store.getERef(tr);
    ERef c_er = er;
    char* tmp = logic.printTerm(tr);
    int written = asprintf(&out, "In the same eq class with %s are:\n[ ",
             tmp);
    assert(written >= 0);
    ::free(tmp);

    while (true) {
        Enode const & en = getEnode(c_er);
        ERef next_er = en.getEqNext();
        if (next_er == er) break;
        Enode const & en_o = getEnode(next_er);
        old = out;
        tmp = logic.printTerm(en_o.getTerm());
        written = asprintf(&out, "%s%s ", old, tmp);
        assert(written >= 0);
        ::free(tmp);
        ::free(old);
        c_er = next_er;
    }
    old = out;
    written = asprintf(&out, "%s]", old);
    assert(written >= 0); (void)written;
    ::free(old);
    return out;
}

std::string Egraph::printExplanationTreeDotty(ERef x)
{
    stringstream os;
    os << "digraph expl" << endl;
    os << "{" << endl;

    while ( x != ERef_Undef ) {
        std::string name = toString(x);
        os << name;
        if (getEnode(x).getExpParent() != ERef_Undef)
            os << " -> ";
        x = getEnode(x).getExpParent();
    }

    os << endl << "}" << endl;
    return os.str();
}

char* Egraph::printDistinctions(PTRef x) const
{
    char* out;
    char* old;

    if (x == PTRef_Undef) {
        assert(false);
        return NULL;
    }

    char* tmp = logic.printTerm(x);
    int written = asprintf(&out, "In different eq class with %s are:\n[ ", tmp);
    assert(written >= 0); (void)written;
    ::free(tmp);


    const ERef er = enode_store[enode_store.getERef(x)].getRoot();

    ELRef elr = enode_store[er].getForbid();
    if (elr == ELRef_Undef) {
        tmp = out;
        written = asprintf(&out, "%s]", tmp);
        assert(written >= 0);
        free(tmp);
        return out;
    }
    ELRef c_elr = elr;

    while (true) {
        const Elist& el = forbid_allocator[c_elr];
        ELRef next_elr = el.link;
        const Elist& el_o = forbid_allocator[next_elr];
        old = out;
        tmp = logic.printTerm(enode_store[el_o.e].getTerm());
        written = asprintf(&out, "%s%s ", old, tmp);
        assert(written >= 0);
        ::free(tmp);
        ::free(old);
        if (next_elr == elr) break;
        c_elr = next_elr;
    }
    old = out;
    written = asprintf(&out, "%s]", old);
    assert(written >= 0);
    ::free(old);
    return out;
}

const string Egraph::printDistinctionList( ELRef x, ELAllocator& ela, bool detailed )
{
    if ( x == ELRef_Undef )
        return "(undef)";

    std::stringstream os;

    ELRef start = x;
    do {
       if (detailed) {
           os << "+-----------------------------------------------------------+" << endl
              << "| Forbid list node                                          |" << endl
              << "+-----------------------------------------------------------+" << endl
              << "| ELRef: " << x.x << endl
              << "| id: " << ela[x].getId() << endl
              << "| dirty: " << ela[x].isDirty() << endl
              << "| reason: " << (ela[x].reason.pta.sgn == l_True ? "" : "not " ) << logic.printTerm(ela[x].reason.pta.tr) << endl;

            if (ela[x].reloced())
                os << "| reloced to: " << ela[x].rel_e.x << endl;
            else {
                os << "| different from enode " << ela[x].e.x << endl;
                os << "|   term " << logic.printTerm(enode_store[ela[x].e].getTerm()) << endl;
            }
            os << "| link: " << ela[x].link.x << endl;
        } else {
            os << "+-----------------------------------------------------------+" << endl
               << "| Forbid list node                                          |" << endl
               << "+-----------------------------------------------------------+" << endl
               << "| reason: " << (ela[x].reason.pta.sgn == l_True ? "" : "not " ) << logic.printTerm(ela[x].reason.pta.tr) << endl;

            os << "| different from enode " << ela[x].e.x << endl;
            os << "|   term " << logic.printTerm(enode_store[ela[x].e].getTerm()) << endl;
        }
        os << "+-----------------------------------------------------------+" << endl;

        x = ela[x].link;
    } while( x != start );
    return os.str();
}

void Egraph::checkForbidReferences(ERef er) {
    ELRef start = enode_store[er].getForbid();
    if (start == ELRef_Undef) return;
    ELRef er_old = start;
    do {
        Elist& e_old = forbid_allocator[er_old];
        for (int j = 0; j < forbid_allocator.referenced_by[e_old.getId()].size(); j++) {
            assert (e_old.e != forbid_allocator.referenced_by[e_old.getId()][j]);
        }
    } while (start != er_old);
}

void Egraph::checkRefConsistency() {
    for (unsigned int i = 0; i < static_cast<unsigned int>(forbid_allocator.referenced_by.size()); i++) {
        vec<ERef>& referers = forbid_allocator.referenced_by[i];
        for (int j = 0; j < referers.size(); j++) {
            ERef referer = referers[j];
            if (referer == ERef_Undef) continue;
            assert(forbid_allocator[enode_store[referer].getForbid()].getId() == i);
        }
    }
}

std::string Egraph::toString(ERef er) const {
    if (er == ERef_Undef) { return "undef"; }
    const Enode & node = getEnode(er);
    return logic.printTerm(node.getTerm());
}
