/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include "Cnfizer.h"
#include "Tseitin.h"

//
// Performs the actual cnfization
//
bool Tseitin::cnfize(PTRef formula
#ifdef PRODUCE_PROOF
                    , const ipartitions_t partitions
#endif
                    )
{
#ifdef PRODUCE_PROOF
    assert( config.produce_inter == 0 || partitions != 0 );
#endif

    assert(formula != PTRef_Undef);
    Pterm& ft = ptstore[formula];
    // Top level formula must not be and anymore
    assert(ft.symb() != sym_AND);

    // Add the top level literal as a unit to solver.
    vec<Lit> clause;
    clause.push(findLit(formula));
#ifdef PRODUCE_PROOF
    if (config.produce_inter != 0)
        solver.addSMTClause(clause, partitions);
#endif
    solver.addSMTClause( clause );

    vec<PTRef> unprocessed_terms;       // Stack for unprocessed terms
    unprocessed_terms.push(formula);    // Start with this term
    //
    // Visit the DAG of the formula
    //
    while (unprocessed_terms.size() != 0) {
        PTRef ptr = unprocessed_terms.last();
        unprocessed_terms.pop();
        //
        // Skip if the node has already been processed before
        //
        if (processed.contains(ptr))
            continue;

        Pterm& pt = ptstore[ptr];
        if (pt.symb() == sym_AND)
            cnfizeAnd(ptr);
        else if (pt.symb() == sym_OR)
            cnfizeOr(ptr);
        else if (pt.symb() == sym_XOR)
            cnfizeXor(ptr);
        else if (pt.symb() == sym_EQ)
            cnfizeIff(ptr);
        else if (pt.symb() != sym_NOT && pt.size() > 0)
            opensmt_error2("operator not handled", symstore.getName(ptstore[ptr].symb()));

        for (int i = 0; i < pt.size(); i++)
            unprocessed_terms.push(pt[i]);

        processed.insert(ptr, true);

    }

    return true;
}


void Tseitin::cnfizeAnd( PTRef and_term
#ifdef PRODUCE_PROOF
                       , const ipartitions_t partitions
#endif
                       )
{
//  assert( list );
//  assert( list->isList( ) );
    //
    // ( a_0 & ... & a_{n-1} )
    //
    // <=>
    //
    // aux = ( -aux | a_0 ) & ... & ( -aux | a_{n-1} ) & ( aux & -a_0 & ... & -a_{n-1} )
    //
    Lit v = findLit(and_term);
    vec<Lit> little_clause;
    vec<Lit> big_clause;
    little_clause.push(~v);
    big_clause   .push(v);
    for (int i = 0; i < ptstore[and_term].size(); i++) {
        PTRef arg = ptstore[and_term][i];
        little_clause.push( findLit(arg));
        big_clause   .push(~findLit(arg));
#ifdef PRODUCE_PROOF
        if ( config.produce_inter > 0 )
            solver.addSMTClause( little_clause, partitions );
        else
#endif
            solver.addSMTClause(little_clause);        // Adds a little clause to the solver
        little_clause.pop();
    }
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
        solver.addSMTClause( big_clause, partitions );
    else
#endif
        solver.addSMTClause( big_clause );                    // Adds a big clause to the solver
}

void Tseitin::cnfizeOr( PTRef or_term
#ifdef PRODUCE_PROOF
                      , const ipartitions_t partitions
#endif
                      )
{
//  assert( list );
//  assert( list->isList( ) );
    //
    // ( a_0 | ... | a_{n-1} )
    //
    // <=>
    //
    // aux = ( aux | -a_0 ) & ... & ( aux | -a_{n-1} ) & ( -aux | a_0 | ... | a_{n-1} )
    //
    vec<Lit>    little_clause;
    vec<Lit>    big_clause;
    Lit v = findLit(or_term);
    little_clause.push( v);
    big_clause   .push(~v);
    for (int i = 0 ; i < ptstore[or_term].size(); i++) {
        Lit arg = findLit(ptstore[or_term][i]);
        little_clause.push(~arg);
        big_clause   .push( arg);
#ifdef PRODUCE_PROOF
        if ( config.produce_inter > 0 )
            solver.addSMTClause( little_clause, partitions );
        else
#endif
            solver.addSMTClause(little_clause);        // Adds a little clause to the solver
        little_clause.pop();
    }
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        solver.addSMTClause( big_clause, partitions );
    else
#endif
            solver.addSMTClause(big_clause);                    // Adds a big clause to the solver
}

void Tseitin::cnfizeXor(PTRef xor_term
#ifdef PRODUCE_PROOF
                       , const ipartitions_t partitions
#endif
                       )
{
    //
    // ( a_0 xor a_1 )
    //
    // <=>
    //
    // aux = ( -aux | a_0  | a_1 ) & ( -aux | -a_0 | -a_1 ) &
    //       (  aux | -a_0 | a_1 ) & (  aux |  a_0 | -a_1 )
    //

    Lit v = findLit(xor_term);

    Lit arg0 = findLit(ptstore[xor_term][0]);
    Lit arg1 = findLit(ptstore[xor_term][1]);
    vec<Lit> clause;

    clause.push(~v);

    // First clause
    clause.push(arg0);
    clause.push(arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        solver.addSMTClause(clause, partitions);
    else
#endif
        solver.addSMTClause(clause); // Adds a little clause to the solver
    clause.pop();
    clause.pop();

    // Second clause
    clause.push(~arg0);
    clause.push(~arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        solver.addSMTClause(clause, partitions);
    else
#endif
        solver.addSMTClause(clause); // Adds a little clause to the solver
    clause.pop();
    clause.pop();

    clause.pop();
    clause.push(v);

    // Third clause
    clause.push(~arg0);
    clause.push( arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        solver.addSMTClause(clause, partitions);
    else
#endif
        solver.addSMTClause(clause); // Adds a little clause to the solver
    clause.pop();
    clause.pop();

    // Fourth clause
    clause.push( arg0);
    clause.push(~arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        solver.addSMTClause(clause, partitions);
    else
#endif
        solver.addSMTClause(clause);           // Adds a little clause to the solver
}

void Tseitin::cnfizeIff( PTRef eq_term
#ifdef PRODUCE_PROOF
                       , const ipartitions_t partitions
#endif
                       )
{

    //
    // ( a_0 <-> a_1 )
    //
    // <=>
    //
    // aux = ( -aux |  a_0 | -a_1 ) & ( -aux | -a_0 |  a_1 ) &
    //       (  aux |  a_0 |  a_1 ) & (  aux | -a_0 | -a_1 )
    //
    assert(ptstore[eq_term].size() == 2);
    Lit v = findLit(eq_term);
    Lit arg0 = findLit(ptstore[eq_term][0]);
    Lit arg1 = findLit(ptstore[eq_term][1]);
    vec<Lit> clause;

    clause.push(~v);

    // First clause
    clause.push( arg0);
    clause.push(~arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        solver.addSMTClause(clause, partitions);
    else
#endif
        solver.addSMTClause(clause);           // Adds a little clause to the solver

    clause.pop();
    clause.pop();

    // Second clause
    clause.push(~arg0);
    clause.push( arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        solver.addSMTClause(clause, partitions);
    else
#endif
        solver.addSMTClause(clause);           // Adds a little clause to the solver

    clause.pop();
    clause.pop();

    clause.pop();
    clause.push(v);

    // Third clause
    clause.push(arg0);
    clause.push(arg1);
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
        solver.addSMTClause(clause, partitions);
    else
#endif
        solver.addSMTClause(clause);           // Adds a little clause to the solver
    clause.pop();
    clause.pop();

    // Fourth clause
    clause.push(~arg0);
    clause.push(~arg1);
#ifdef PRODUCE_PROOF
    if (config.produce_inter > 0)
        solver.addSMTClause(clause, partitions);
    else
#endif
        solver.addSMTClause(clause);           // Adds a little clause to the solver
}

/*
void Tseitin::cnfizeIfthenelse( Enode * list
                              , Enode * arg_def
#ifdef PRODUCE_PROOF
                              , const ipartitions_t partitions
#endif
                              )
{
  if ( arg_def == NULL )
  {
    Enode * i = list->getCar();
    Enode * t = list->getCdr( )->getCar( );
    Enode * e = list->getCdr( )->getCdr( )->getCar( );

    vector< Enode * > clause;

    clause.push_back( toggleLit( i ) );
    clause.push_back( t );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );        

    clause.pop_back( );
    clause.pop_back( );

    clause.push_back( i );
    clause.push_back( e );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );        
  }
  else
  {
    //  (!a | !i | t) & (!a | i | e) & (a | !i | !t) & (a | i | !e)
    //
    // ( if a_0 then a_1 else a_2 )
    //
    // <=>
    //
    // aux = ( -aux | -a_0 |  a_1 ) &
    //       ( -aux |  a_0 |  a_2 ) &
    //       (  aux | -a_0 | -a_1 ) &
    //       (  aux |  a_0 | -a_2 )
    //
    assert( list->getArity( ) == 3 );
    Enode * arg0 = list->getCar( );
    Enode * arg1 = list->getCdr( )->getCar( );
    Enode * arg2 = list->getCdr( )->getCdr( )->getCar( );
    vector< Enode * > clause;

    clause.push_back( toggleLit( arg_def ) );

    // First clause
    clause.push_back( toggleLit( arg0 ) );
    clause.push_back( arg1 );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );
    clause.pop_back( );
    clause.pop_back( );

    // Second clause
    clause.push_back( arg0 );
    clause.push_back( arg2 );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );
    clause.pop_back( );
    clause.pop_back( );

    clause.pop_back( );
    clause.push_back( arg_def );

    // Third clause
    clause.push_back( toggleLit( arg0 ) );
    clause.push_back( toggleLit( arg1 ) );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );
    clause.pop_back( );
    clause.pop_back( );

    // Fourth clause
    clause.push_back( arg0 );
    clause.push_back( toggleLit( arg2 ) );
#ifdef PRODUCE_PROOF
    if ( config.produce_inter > 0 )
      solver.addSMTClause( clause, partitions );
    else
#endif
    solver.addSMTClause( clause );
  }
}
*/

