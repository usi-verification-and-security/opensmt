/*
 *  Copyright (c) 2013, Simone Fulvio Rollini <simone.rollini@gmail.com>
 *  Copyright (c) 2020-2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "PG.h"

#include "OsmtInternalException.h"
#include "VerificationUtils.h"

bool
ProofGraph::verifyPartialInterpolant(ProofNode const & n, const ipartitions_t& mask)
{
    if(verbose())
        std::cout << "; Verifying partial interpolant" << '\n';
    bool res = verifyPartialInterpolantA(n, mask);
    if(!res)
    {
        assert(false);
        throw OsmtInternalException("Partial interpolant soundness does not hold for A");
    }
    res = verifyPartialInterpolantB(n, mask);
    if(!res)
    {
        assert(false);
        throw OsmtInternalException("Partial interpolant soundness does not hold for B");
    }
    if(verbose())
        std::cout << "; Partial interpolant is sound" << '\n';
    return res;
}

bool
ProofGraph::verifyPartialInterpolantA(ProofNode const & n, const ipartitions_t& mask)
{
    // Check A /\ ~(C|a,ab) -> I, i.e., A /\ ~(C|a,ab) /\ ~I unsat
    Logic& logic = this->logic_;
    icolor_t var_class;
    icolor_t var_color;
    std::vector< Lit > const & cl = n.getClause();
    vec<PTRef> restricted_clause;

    const size_t size = cl.size( );
    for( size_t i = 0 ; i < size ; i ++ )
    {
        Var v = var(cl[i]);
        var_class = getVarClass2( v );
        assert( var_class == icolor_t::I_B || var_class == icolor_t::I_A || var_class == icolor_t::I_AB );
        if( var_class == icolor_t::I_B || var_class == icolor_t::I_A ) var_color = var_class;
        else
        {
            // Determine color of AB variable
            if( isColoredA( n,v ) ) var_color = icolor_t::I_A;
            else if ( isColoredB( n,v )  ) var_color = icolor_t::I_B;
            else if ( isColoredAB( n,v ) ) var_color = icolor_t::I_AB;
            else throw OsmtInternalException("Variable " + std::to_string(v) + " has no color in clause " + std::to_string(n.getId()));
        }
        if( var_color == icolor_t::I_A || var_color == icolor_t::I_AB )
        {
            PTRef ptaux = varToPTRef(var(cl[i]));
            if(sign(cl[i]))
                ptaux = logic.mkNot(ptaux);
            restricted_clause.push(ptaux);
        }
    }

    PTRef cl_ptref = logic.mkNot(logic.mkOr(std::move(restricted_clause)));
    PTRef implicant = logic.mkAnd({pmanager.getPartition(mask, PartitionManager::part::A), cl_ptref});

    /*
    cout << "; MASK IS " << mask << endl;
    cout << "; PARTITION A IS " << logic.printTerm(logic.getPartitionA(mask)) << endl;
    cout << "; TCLAUSE IS " << logic.printTerm(cl_ptref) << endl;
    cout << "; PARTIAL INTERPOLANT IS " << logic.printTerm(n->getPartialInterpolant()) << endl;
    */

    bool res = VerificationUtils(config, logic).impliesExternal(implicant, n.getPartialInterpolant());
    assert(res);
    return res;
}

bool
ProofGraph::verifyPartialInterpolantB(ProofNode const & n, const ipartitions_t& mask)
{
    // Check B /\ ~(C|b,ab) -> ~I, i.e., B /\ ~(C|b,ab) /\ I unsat 
    Logic& logic = this->logic_;
    icolor_t var_class;
    icolor_t var_color;
    std::vector< Lit > const & cl = n.getClause();
    vec<PTRef> restricted_clause;

    const size_t size = cl.size( );
    for( size_t i = 0 ; i < size ; i ++ )
    {
        Var v = var(cl[i]);
        var_class = getVarClass2( v );
        assert( var_class == icolor_t::I_B || var_class == icolor_t::I_A || var_class == icolor_t::I_AB );
        if( var_class == icolor_t::I_B || var_class == icolor_t::I_A ) var_color = var_class;
        else
        {
            // Determine color of AB variable
            if( isColoredA( n,v ) ) var_color = icolor_t::I_A;
            else if ( isColoredB( n,v )  ) var_color = icolor_t::I_B;
            else if ( isColoredAB( n,v ) ) var_color = icolor_t::I_AB;
            else throw OsmtInternalException("Variable " + std::to_string(v) + " has no color in clause " + std::to_string(n.getId()));
        }
        if( var_color == icolor_t::I_B || var_color == icolor_t::I_AB )
        {
            PTRef ptaux = varToPTRef(var(cl[i]));
            if(sign(cl[i]))
                ptaux = logic.mkNot(ptaux);
            restricted_clause.push(ptaux);
        }
    }

    PTRef cl_ptref = logic.mkNot(logic.mkOr(std::move(restricted_clause)));
    PTRef implicant = logic.mkAnd({pmanager.getPartition(mask, PartitionManager::part::B), cl_ptref});

    /*
    cout << "; MASK IS " << mask << endl;
    cout << "; PARTITION B IS " << logic.printTerm(logic.getPartitionB(mask)) << endl;
    cout << "; TCLAUSE IS " << logic.printTerm(cl_ptref) << endl;
    cout << "; PARTIAL INTERPOLANT IS " << logic.printTerm(n->getPartialInterpolant()) << endl;
    */

    bool res = VerificationUtils(config, logic).impliesExternal(implicant, logic.mkNot(n.getPartialInterpolant()));
    assert(res);
    return res;
}
