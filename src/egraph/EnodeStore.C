#include "EnodeStore.h"
#include "Symbol.h"

ERef EnodeStore::addSymb(SymRef t) {
    ERef rval;
    assert(t != SymRef_Undef);
    if (symToERef.contains(t))
        rval = symToERef[t];
    else {
        ERef er = ea.alloc(t);
        symToERef.insert(t, er);
        rval = er;
#ifdef PEDANTIC_DEBUG
        enodes.push(er);
#endif
    }
    return rval;
}

// Here we try a clever trick to avoid having to introduce enodes to
// terms that are in the same equivalence class with another enode
// already inserted.
ERef EnodeStore::addTerm(ERef sr, ERef args, PTRef term) {
    ERef rval;
    if (termToERef.contains(term))
        rval = termToERef[term];
    else {
        // Term's signature might be here already, and then it should
        // join the equivalence group.  There is a bit of a challenge,
        // however: if the term goes there as a result of an eariler
        // asserted equality which is then undone, the entry in
        // termToERef is invalidated.  The term should be then removed
        // together with the undoing so that it can be reasserted.  What
        // happens in this case to the non-allocated enode?  It will be
        // allocated once reasserted.
        if (containsSig(sr, args)) {
            rval = lookupSig(sr, args);
            termToERef.insert(term, rval);
            ERefToTerms[rval].push(term);
//            cerr << "letting " << term_store.printTerm(term)
//                 << " point to %s" << printEnode(rval) << endl;
//            assert(false); // XXX push to the undo stack
        }
        else {
            rval = ea.alloc(sr, args, Enode::et_term, term);
            insertSig(rval);
            termToERef.insert(term, rval);
            vec<PTRef> terms;
            terms.push(term);
            ERefToTerms.insert(rval, terms);
#ifdef PEDANTIC_DEBUG
            enodes.push(rval);
#endif
        }
    }
    return rval;
}

ERef EnodeStore::cons(ERef x, ERef y) {
    ERef rval;
    if (!containsSig(x, y)) {
        rval = ea.alloc(x, y, Enode::et_list, PTRef_Undef);
        insertSig(rval);
#ifdef PEDANTIC_DEBUG
        enodes.push(rval);
#endif
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

// p is only given as an argument for assertion checking!
void EnodeStore::removeParent(ERef n, ERef p) {

    if ( n == ERef_Nil ) return;

    Enode& en_n = ea[n];

    assert( en_n.isList() || en_n.isTerm( ) );
    assert( en_n.getParent() != ERef_Undef );
    assert( en_n.getParentSize() > 0 );
    en_n.setParentSize( en_n.getParentSize() - 1 );
    // If only one parent, remove it and restore NULL
    if ( en_n.getParentSize() == 0 )
    {
        assert( en_n.getParent() == p );
        en_n.setParent( ERef_Undef );
        return;
    }
    // Otherwise adds remove p from the samecar/cdr list
    if ( en_n.isList() )
    {
        // Build or update samecdr circular list
        assert( ea[en_n.getParent()].getSameCdr() == p );
        Enode& en_samecdr = ea[ea[en_n.getParent()].getSameCdr()];
        ea[en_n.getParent()].setSameCdr( en_samecdr.getSameCdr() );
    }
    else
    {
        // Build or update samecar circular list
        assert( ea[en_n.getParent()].getSameCar() == p );
        Enode& en_samecar = ea[ea[en_n.getParent()].getSameCar()];
        ea[en_n.getParent()].setSameCar( en_samecar.getSameCar( ) );
    }
}

// DEBUG

std::string EnodeStore::printEnode(ERef e) {
    Enode& en = ea[e];
    std::stringstream s;
    s <<         "+=============================================" << endl;
    if (en.isTerm()) {
        s <<     "| Term enode (" << term_store.printTerm(en.getTerm()) << ")" << endl
          <<     "+---------------------------------------------" << endl
          <<     "|  - Reference : " << e.x << endl
          <<     "|  - Symb Enode: " << en.getCar().x  << endl
          <<     "|  - List Enode: " << en.getCdr().x  << endl
          <<     "|  - root      : " << en.getRoot().x << endl
          <<     "|  - congruence: " << en.getCid()    << endl
          <<     "|  - root cong.: " << ea[en.getRoot()].getCid() << endl
          <<     "|  - cong. ptr : " << en.getCgPtr().x<< endl
          <<     "+---------------------------------------------" << endl;
    }

    else if (en.isList()) {
        s <<     "| List enode                                 |" << endl
          <<     "+--------------------------------------------+" << endl
          <<     "|  - Reference : " << e.x << endl
          <<     "|  - Car       : " << en.getCar().x  << endl
          <<     "|  - Cdr       : " << en.getCdr().x  << endl
          <<     "|  - root      : " << en.getRoot().x << endl
          <<     "|  - congruence: " << en.getCid()    << endl
          <<     "|  - root cong.: " << ea[en.getRoot()].getCid() << endl
          <<     "|  - cong. ptr : " << en.getCgPtr().x<< endl
          <<     "+--------------------------------------------+" << endl;
    }

    else if (en.isSymb()) {
        s <<     "| Symb enode (" << sym_store.getName(en.getSymb()) << ")" << endl
          <<     "+---------------------------------------------" << endl
          <<     "|  - Reference: " << e.x << endl
          <<     "+=============================================" << endl;
    }
    if (!en.isSymb()) {
        s <<     "|  - Number of parents: " << ea[en.getRoot()].getParentSize() << endl
          <<     "|    ";
        ERef parent_start = en.getParent();
        ERef parent = parent_start;
        int pcount = 0;
        if (parent_start == ERef_Undef) { s << endl; goto skip; }
        if (en.isTerm()) {
            while (true) {
                pcount ++;
                s << parent.x << " ";
                parent = ea[parent].getSameCar();
                if (parent == parent_start) break;
            }
        }
        else if (en.isList()) {
            ERef parent_start = en.getParent();
            ERef parent = parent_start;
            while (true) {
                pcount ++;
                s << parent.x << " ";
                parent = ea[parent].getSameCdr();
                if (parent == parent_start) break;
            }
        }
        if (pcount != ea[en.getRoot()].getParentSize())
            s << "parent count mismatch!";
        s << endl;
skip:
        if (en.isTerm()) {
            s << printEnode(en.getCar()) << endl;
            ERef cdr = en.getCdr();
            if (cdr != ERef_Nil) {
                s << printEnode(cdr) << endl;
            }
        }
        else if (en.isList()) {
            s << printEnode(en.getCar());
            if (en.getCdr() != ERef_Nil)
                s << printEnode(en.getCdr());
        }
    }
    return s.str();
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

