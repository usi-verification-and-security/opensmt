#include "EnodeStore.h"
#include "Term.h"

ERef EnodeStore::addSymb(TRef t) {
    ERef rval;
    if (symToERef.contains(t))
        rval = symToERef[t];
    else {
        ERef er = ea.alloc(t);
        symToERef.insert(t, er);
        rval = er;
    }
    return rval;
}

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
            assert(false); // XXX push to the undo stack
        }
        else {
            rval = ea.alloc(sr, args, Enode::et_term, term);
            insertSig(rval);
            termToERef.insert(term, rval);
        }
    }
    return rval;
}

ERef EnodeStore::cons(ERef x, ERef y) {
    ERef rval;
    if (!containsSig(x, y)) {
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
