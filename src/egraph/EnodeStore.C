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
ERef EnodeStore::addTerm(ERef sr, ERef args, PTRef term, int level) {
    assert(ea[sr].isSymb());
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
            bool is_edn = (ea[args].getRoot() != args);
            if (is_edn) {
#ifdef PEDANTIC_DEBUG
                cerr << "Non-root args" << endl;
#endif
                args = ea[args].getRoot();
            }
            rval = ea.alloc(sr, args, Enode::et_term, term);
            if (is_edn) {
                EqDepId edi(rval, level);
                if (!eq_dep_conses.contains(args)) {
                    vec<EqDepId> tmp;
                    eq_dep_conses.insert(args, tmp);
                }
                eq_dep_conses[args].push(edi);
            }
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

// Same cleverness implemented here.
// Problem: Parent invariants are broken if x or y is not a congruence root.
ERef EnodeStore::addList(ERef x, ERef y, int level) {
    ERef rval;
    // This is skipped if there is a term corresponding to cons of these guys equivalence class,
    // but goes through also in case x and y are not equivalence roots but no cons corresponding to the
    // equivalence roots exist.
    if (!containsSig(x, y)) {
        bool is_edn_x = (ea[x].getRoot() != x);
        ERef old_x = x;
        if (is_edn_x) {
#ifdef PEDANTIC_DEBUG
            cerr << "Non-root car" << endl;
#endif
            x = ea[x].getRoot();
        }
        bool is_edn_y = (ea[y].getRoot() != y);
        ERef old_y = y;
        if (is_edn_y) {
#ifdef PEDANTIC_DEBUG
            cerr << "Non-root cdr" << endl;
#endif
            y = ea[y].getRoot();
        }
        rval = ea.alloc(x, y, Enode::et_list, PTRef_Undef);
        if (is_edn_x) {
            EqDepId edi(rval, level);
            if (!eq_dep_conses.contains(old_x)) {
                vec<EqDepId> tmp;
                eq_dep_conses.insert(old_x, tmp);
            }
            eq_dep_conses[old_x].push(edi);
        }
        if (is_edn_y) {
            EqDepId edi(rval, level);
            if (!eq_dep_conses.contains(old_y)) {
                vec<EqDepId> tmp;
                eq_dep_conses.insert(old_y, tmp);
            }
            eq_dep_conses[old_y].push(edi);
        }
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

// Undo a term.  Prerequisites are that the node has no parents
// and is in a singleton equivalence class.
void EnodeStore::undoTerm( ERef e ) {
    assert( e != ERef_Nil );
    assert( ea[e].isTerm() );
    assert( ea[e].getParentSize() == 0 );
    assert( ea[e].getNext() == e );

    Enode& en = ea[e];
    ERef car = en.getCar();
    ERef cdr = en.getCdr();

    // Node must be there
    assert( lookupSig(e) == e );
    // Remove from sig_tab
    removeSig(e);
    // Remove Parent info
    Enode& en_car = ea[car];
    Enode& en_cdr = ea[cdr];

    assert(en_car.isSymb());
    assert(en_cdr.isList() || cdr == ERef_Nil);

    // remove e from cdr's parent list
    if (cdr != ERef_Nil) {
        assert(en_cdr.getParentSize() > 0);
        int parentsz = en_cdr.getParentSize();
        if (parentsz == 1) {
            en_cdr.setParentSize(0);
            en_cdr.setParent(ERef_Undef);
        }
        else {
            ERef p = en_cdr.getParent();
            ERef p_prev;
            while (true) {
                p_prev = p;
                p = ea[p].getSameCdr();
                if (p == e) break;
            }
            assert(p == e);
            ea[p_prev].setSameCdr(en.getSameCdr());
        }
        en_cdr.setParentSize(parentsz-1);
    }

    // Get rid of the extra data
    termToERef.remove(en.getTerm());
    ERefToTerms.remove(e);
    ea.free(e);
}

// Undo a list.  Prerequisites are that the node has no parents
// and is in a singleton equivalence class.
void EnodeStore::undoList( ERef e ) {
    assert( e != ERef_Nil );
    assert( ea[e].isList() );
    assert( ea[e].getParentSize() == 0 );
    assert( ea[e].getNext() == e );

    Enode& en = ea[e];
    ERef car = en.getCar();
    ERef cdr = en.getCdr();

    // Node must be there
    assert( lookupSig(e) == e );
    // Remove from sig_tab
    removeSig(e);
    // Remove Parent info
    Enode& en_car = ea[car];
    Enode& en_cdr = ea[cdr];

    assert(en_car.isTerm());
    assert(en_cdr.isList() || cdr == ERef_Nil);

    // remove e from cdr's parent list
    if (cdr != ERef_Nil) {
        assert(en_cdr.getParentSize() > 0);
        int parentsz = en_cdr.getParentSize();
        if (parentsz == 1) {
            en_cdr.setParentSize(0);
            en_cdr.setParent(ERef_Undef);
        }
        else {
            ERef p = en_cdr.getParent();
            ERef p_prev;
            while (true) {
                p_prev = p;
                p = ea[p].getSameCdr();
                if (p == e) break;
            }
            assert(p == e);
            ea[p_prev].setSameCdr(en.getSameCdr());
        }
        en_cdr.setParentSize(parentsz-1);
    }

    // remove e from car's parent list
    assert(en_cdr.getParentSize() > 0);
    int parentsz = en_car.getParentSize();
    if (parentsz == 1) {
        en_car.setParentSize(0);
        en_car.setParent(ERef_Undef);
    }
    else {
        ERef p = en_car.getParent();
        ERef p_prev;
        while (true) {
            p_prev = p;
            p = ea[p].getSameCar();
            if (p == e) break;
        }
        assert(p == e);
        ea[p_prev].setSameCar(en.getSameCar());
    }
    en_car.setParentSize(parentsz-1);

    ea.free(e);
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

