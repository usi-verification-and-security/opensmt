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


#include "EnodeStore.h"
#include "Symbol.h"
#include "Logic.h"

ERef EnodeStore::addSymb(SymRef t) {
    ERef rval;
    assert(t != SymRef_Undef);
    if (symToERef.has(t))
        rval = symToERef[t];
    else {
        ERef er = ea.alloc(t);
        symToERef.insert(t, er);
        rval = er;

//        enodes.push(er);

    }
    return rval;
}

//
// Add a term to enode store
//
PTRef EnodeStore::addTerm(ERef sr, ERef args, PTRef term) {
    assert(ea[sr].isSymb());
    PTRef rval;
    if (termToERef.has(term))
        rval = term;
    else {
        // Term's signature might be here already, and then it should
        // join the equivalence group.  To have the explanations
        // working, there must not be two terms that correspond to a
        // single enode (this goes back to the explanation tree).  Thus
        // we need to communicate equality back to the caller so that
        // eventually required actions can be taken.
        if (containsSig(sr, args)) {
            assert(false);
            ERef canon = lookupSig(sr, args);
            termToERef.insert(term, canon);
            rval = ea[canon].getTerm();
#ifdef PEDANTIC_DEBUG
            cerr << "Seeing the duplicate in EnodeStore: "
                 << "ERef " << canon.x << endl;
            char* enstr = printEnode(canon);
            cerr << "letting " << logic.printTerm(term)
                 << " point to " << endl << enstr << endl;
            ::free(enstr);
#endif
        }
        else {
            assert (ea[args].getRoot() == args);
            ERef new_er = ea.alloc(sr, args, Enode::et_term, term);
            insertSig(new_er);
            termToERef.insert(term, new_er);
            assert(!ERefToTerm.has(new_er));
            ERefToTerm.insert(new_er, term);

            termEnodes.push(new_er);

            rval = term;
        }
    }
    return rval;
}

// Same cleverness implemented here.
// Problem: Parent invariants are broken if x or y is not a congruence root.
ERef EnodeStore::addList(ERef x, ERef y) {
    ERef rval;
    // This is skipped if there is a term corresponding to cons of these guys equivalence class,
    // but goes through also in case x and y are not equivalence roots but no cons corresponding to the
    // equivalence roots exist.
    if (!containsSig(x, y)) {
        assert(ea[x].getRoot() == x);
        assert(ea[y].getRoot() == y);

        rval = ea.alloc(x, y, Enode::et_list, PTRef_Undef);
        insertSig(rval);

    }
    else {
        // Again this could be because of an asserted equality.  If the
        // equality is retracted, the list might need to be
        // reintroduced.  However, the term introduction should take
        // care of this.
        rval = lookupSig(x, y);
    }
    return rval;
}

// DEBUG

char* EnodeStore::printEnode(ERef e) {
    Enode& en = ea[e];
    char* out;
    char* old;
    asprintf(&out, "+=============================================\n");

    if (en.isTerm()) {
        old = out;
        asprintf(&out, "%s| Term enode (%s)\n"
                         "+---------------------------------------------\n"
                         "|  - Reference : %d\n"
                         "|  - Symb Enode: %d\n"
                         "|  - List Enode: %d\n"
                         "|  - root      : %d\n"
                         "|  - congruence: %d\n"
                         "|  - root cong.: %d\n"
                         "|  - cong. ptr : %d\n"
                         "+---------------------------------------------\n"
                         "| Forbids: \n"
#ifndef PEDANTIC_DEBUG
                         "|   N/A (enable debug)\n"
#endif
                     , old
                     , logic.printTerm(en.getTerm())
                     , e.x
                     , en.getCar().x
                     , en.getCdr().x
                     , en.getRoot().x
                     , en.getCid()
                     , ea[en.getRoot()].getCid()
                     , en.getCgPtr().x);
        ::free(old);
#ifdef PEDANTIC_DEBUG
        ELRef f_start = en.getForbid();
        ELRef f_next = f_start;
        if (f_start != ELRef_Undef) {
            while (true) {
                old = out;
                asprintf(&out, "%s %d (%s) ",
                    old,
                    f_next.x,
                    logic.printTerm((operator[] (fa[f_next].e)).getTerm()));
                ::free(old);
                f_next = fa[f_next].link;
                if (f_next == f_start) break;
            }
        }
        old = out;
        asprintf(&out, "%s\n+---------------------------------------------\n", old);
        ::free(old);
#endif

    }

    else if (en.isList()) {
        old = out;
        asprintf(&out, "%s| List enode                                 |\n"
                         "+--------------------------------------------+\n"
                         "|  - Reference : %d\n"
                         "|  - Car       : %d\n"
                         "|  - Cdr       : %d\n"
                         "|  - root      : %d\n"
                         "|  - congruence: %d\n"
                         "|  - root cong.: %d\n"
                         "|  - cong. ptr : %d\n"
                         "+--------------------------------------------+\n"
                     , old
                     , en.getCdr().x
                     , e.x
                     , en.getCar().x
                     , en.getRoot().x
                     , en.getCid()
                     , ea[en.getRoot()].getCid()
                     , en.getCgPtr().x);
        ::free(old);
    }

    else if (en.isSymb()) {
        old = out;
        asprintf(&out, "%s| Symb enode (%s)\n"
                         "+---------------------------------------------\n"
                         "|  - Reference: %d\n"
                         "+=============================================\n"
                     , old, logic.getSymName(en.getSymb())
                     , e.x);
        ::free(old);

    }
    if (!en.isSymb()) {
        old = out;
        asprintf(&out, "%s|  - Number of parents: %d\n"
                         "|    "
                     , old, ea[en.getRoot()].getParentSize());
        ::free(old);
        ERef parent_start = en.getParent();
        ERef parent = parent_start;
        int pcount = 0;
        if (parent_start == ERef_Undef) {
            old = out;
            asprintf(&out, "%s\n", old);
            ::free(old);
            goto skip; }
        if (en.isTerm()) {
            while (true) {
                old = out;
                pcount ++;
                asprintf(&out, "%s%d ", old, parent.x);
                ::free(old);
                parent = ea[parent].getSameCar();
                if (parent == parent_start) break;
            }
        }
        else if (en.isList()) {
            ERef parent_start = en.getParent();
            ERef parent = parent_start;
            while (true) {
                old = out;
                pcount ++;
                asprintf(&out, "%s%d ", old, parent.x);
                ::free(old);
                parent = ea[parent].getSameCdr();
                if (parent == parent_start) break;
            }
        }
        if (pcount != ea[en.getRoot()].getParentSize()) {
            old = out;
            asprintf(&out, "%s%s", old, "parent count mismatch!");
            ::free(old);
        }
        old = out;
        asprintf(&out, "%s\n", old);
        ::free(old);
skip:
        if (en.isTerm()) {
            old = out;
            char* in = printEnode(en.getCar());
            asprintf(&out, "%s%s\n", old, in);
            ::free(old);
            ::free(in);
            ERef cdr = en.getCdr();
            if (cdr != ERef_Nil) {
                old = out;
                in = printEnode(cdr);
                asprintf(&out, "%s%s\n", old, in);
                ::free(old);
                ::free(in);
            }
        }
        else if (en.isList()) {
            old = out;
            char* in = printEnode(en.getCar());
            asprintf(&out, "%s%s", old, in);
            ::free(old);
            ::free(in);
            if (en.getCdr() != ERef_Nil) {
                old = out;
                in = printEnode(en.getCdr());
                asprintf(&out, "%s%s", old, in);
                ::free(old);
                ::free(in);
            }
        }
    }
    return out;
}

#ifdef PEDANTIC_DEBUG
bool EnodeStore::checkInvariants( )
{
    // Check all enodes
    for ( int first = 0 ; first < enodes.size( ) ; first ++ ) {
        assert ( enodes[first] != ERef_Undef );
        ERef e = enodes[first];
        if (ea[e].isSymb()) continue;

        assert(containsSig(e));
        ERef root = lookupSig(e);
        Enode& en_r = ea[root];
        assert(en_r.isTerm() || en_r.isList());
        // The sigtab contains elements ((x.car.root.id, x.cdr.root.id), x)
        // such that x is a binary E/node that is a congruence root
        if ( root != en_r.getCgPtr() ) {
            cerr << "STC Invariant broken: "
                 << root.x
                 << " is not congruence root"
                 << endl;
            assert(false);
        }
    }

    // Check all signatures, but I'm not sure what exactly I want to check here
//    if ( x->getSig( ) != p ) {
//        cerr << "x root: " << x->getRoot( ) << endl;
//        cerr << "x root car: " << x->getRoot( )->getCar( ) << endl;
//        cerr << "x root car root: " << x->getRoot( )->getCar( )->getRoot( ) << endl;
//        cerr << "x->getCar( ): " << x->getCar( )->getId( ) << endl;
//        cerr << "STC Invariant broken: "
//             << x
//             << " signature is wrong."
//             << " It is "
//             << "(" << x->getSigCar( )
//             << ", " << x->getSigCdr( )
//             << ") instead of ("
//             << p.first
//             << ", "
//             << p.second
//             << ")"
//             << endl;
//        return false;
//    }

    return true;
}
#endif

