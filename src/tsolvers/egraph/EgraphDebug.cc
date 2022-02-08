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


std::string Egraph::printEqClass(PTRef tr) const {
    std::stringstream out;
    const ERef er = enode_store.getERef(tr);
    ERef c_er = er;
    out << "In the same eq class with " << logic.printTerm(tr) << " are:\n[ ";

    while (true) {
        Enode const & en = getEnode(c_er);
        ERef next_er = en.getEqNext();
        if (next_er == er) break;
        Enode const & en_o = getEnode(next_er);
        out << logic.printTerm(en_o.getTerm()) << ' ';
    }
    out << "]";
    return out.str();
}

std::string Egraph::printExplanationTreeDotty(ERef x) const {
    std::stringstream os;
    os << "digraph expl" << '\n';
    os << "{" << '\n';

    while ( x != ERef_Undef ) {
        std::string name = toString(x);
        os << name;
        if (getEnode(x).getExpParent() != ERef_Undef)
            os << " -> ";
        x = getEnode(x).getExpParent();
    }

    os << '\n' << "}" << '\n';
    return os.str();
}

std::string Egraph::printDistinctions(PTRef x) const
{
    if (x == PTRef_Undef) {
        assert(false);
        return "";
    }

    std::stringstream out;
    out << "In different eq class with " << logic.printTerm(x) << " are:\n[ ";

    const ERef er = enode_store[enode_store.getERef(x)].getRoot();

    ELRef elr = enode_store[er].getForbid();
    if (elr == ELRef_Undef) {
        out << ']';
        return out.str();
    }
    ELRef c_elr = elr;

    while (true) {
        const Elist& el = forbid_allocator[c_elr];
        ELRef next_elr = el.link;
        const Elist& el_o = forbid_allocator[next_elr];
        out << logic.printTerm(enode_store[el_o.e].getTerm()) << ' ';
        if (next_elr == elr) break;
        c_elr = next_elr;
    }
    out << ']';
    return out.str();
}

const std::string Egraph::printDistinctionList( ELRef x, ELAllocator& ela, bool detailed )
{
    if ( x == ELRef_Undef )
        return "(undef)";

    std::stringstream os;

    ELRef start = x;
    do {
       if (detailed) {
           os << "+-----------------------------------------------------------+" << '\n'
              << "| Forbid list node                                          |" << '\n'
              << "+-----------------------------------------------------------+" << '\n'
              << "| ELRef: " << x.x << '\n'
              << "| id: " << ela[x].getId() << '\n'
              << "| dirty: " << ela[x].isDirty() << '\n'
              << "| reason: " << (ela[x].reason.pta.sgn == l_True ? "" : "not " ) << logic.printTerm(ela[x].reason.pta.tr) << '\n';

            if (ela[x].reloced())
                os << "| reloced to: " << ela[x].rel_e.x << '\n';
            else {
                os << "| different from enode " << ela[x].e.x << '\n';
                os << "|   term " << logic.printTerm(enode_store[ela[x].e].getTerm()) << '\n';
            }
            os << "| link: " << ela[x].link.x << '\n';
        } else {
            os << "+-----------------------------------------------------------+" << '\n'
               << "| Forbid list node                                          |" << '\n'
               << "+-----------------------------------------------------------+" << '\n'
               << "| reason: " << (ela[x].reason.pta.sgn == l_True ? "" : "not " ) << logic.printTerm(ela[x].reason.pta.tr) << '\n';

            os << "| different from enode " << ela[x].e.x << '\n';
            os << "|   term " << logic.printTerm(enode_store[ela[x].e].getTerm()) << '\n';
        }
        os << "+-----------------------------------------------------------+" << '\n';

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
