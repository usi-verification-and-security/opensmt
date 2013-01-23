#include "EnodeStore.h"
#include "Term.h"

ERef EnodeStore::addSymb(TRef t) {
    return ea.alloc(t);
}

ERef EnodeStore::addTerm(ERef sr) {
    return ea.alloc(sr, ERef_Nil, Enode::et_term);
}

ERef EnodeStore::cons(ERef x, ERef y) {
    return ea.alloc(x, y, Enode::et_list);
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
        setParent( ERef_Undef );
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
        assert( ea[ea_n.getParent()].getSameCar() == p );
        Enode& en_samecar = ea[ea[en_n.getParent()].getSameCar()];
        ea[en_n.getParent()].setSameCar( en_samecar.getSameCar( ) );
    }
}
