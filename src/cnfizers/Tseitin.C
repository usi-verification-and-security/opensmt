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
    // Top level formula must not be and anymore
    assert(ptstore[formula].symb() != sym_AND);

    if (processed.contains(formula)) {
        //
        // Formula was cnfized before ...
        //
        vec<Lit> clause;
        clause.push(findLit(formula));
#ifdef PRODUCE_PROOF
        if (config.produce_inter != 0)
            return solver.addSMTClause(clause, partitions);
#endif
        return solver.addSMTClause( clause );
    }

    vec<PTRef> unprocessed_terms;       // Stack for unprocessed terms
    unprocessed_terms.push(formula);    // formula needs to be processed
    //
    // Visit the DAG of the formula from the leaves to the root
    //
    while (unprocessed_terms.size() != 0) {
        PTRef ptr = unprocessed_terms.last();
        unprocessed_terms.pop();
        //
        // Skip if the node has already been processed before
        //
        if (processed.contains(ptr)) {
            unprocessed_terms.pop();
            continue;
        }

        bool unprocessed_children = false;
        Pterm& pt = ptstore[ptr];
        for (int i = 0; i < pt.size(); i++) {

            PTRef arg = pt[i];
            Pterm arg_t = ptstore[arg];
            if (isBooleanOperator(arg_t.symb()) && !processed.contains(arg)) {
                unprocessed_terms.push(arg);
                unprocessed_children = true;
            }
            //
            // If it is an unseen atom (either boolean or theory) introduce a new lit for it and
            // store it in the cache.  If it is a constant true or false, introduce the corresponding literals.
            //
            else if (isAtom(arg)) declareAtom(arg, arg_t.symb());
        }
        //
        // Skip if unprocessed_children.
        //
        if ( unprocessed_children )
            continue;

        assert(unprocessed_terms.size() == 0);
        Lit result = lit_Undef;
        //
        // At this point, every child of ptr has been processed
        //
        //
        // Do the actual cnfization, according to the node type
        //
//        char def_name[ 32 ];

        if (isLit(ptr)) ;
//            result = ptr;
        else if (pt.symb() == sym_NOT) {
            assert(processed.contains(ptstore[ptr][0]));
            Var v = processed.contains(ptstore[ptr][0]);
            result = Lit(v, true);
        }
        else {
            //
            // If the term is not top-level it needs a definition
            //
            Lit v = lit_Undef;
            if (formula != ptr) {
                v = Lit(solver.newVar());
#ifdef PRODUCE_PROOF
                if ( config.produce_inter != 0 ) {
                    arg_def->setIPartitions( partitions );
                    egraph.addDefinition( arg_def, enode );
                }
#endif
            }
            //
            // Handle boolean operators
            //
            if (pt.symb() == sym_AND)
                cnfizeAnd( ptr
                         , v
#ifdef PRODUCE_PROOF
                         , partitions
#endif
                );
            else if (pt.symb() == sym_OR)
                cnfizeOr( ptr
                        , v
#ifdef PRODUCE_PROOF
                        , partitions
#endif
                );
            else if (pt.symb() == sym_EQ)
                cnfizeIff(ptr
                         , v
#ifdef PRODUCE_PROOF
                         , partitions
#endif
                );
            else if (pt.symb() == sym_XOR)
                cnfizeXor(ptr
                         , v
#ifdef PRODUCE_PROOF
                         , partitions
#endif
                         );
            else opensmt_error2("operator not handled", symstore.getName(ptstore[ptr].symb()));

            if (v != lit_Undef)
                result = v;
        }

//    assert( egraph.valDupMap1( enode ) == NULL );
//    egraph.storeDupMap1( enode, result );
    }

//  if ( formula->isNot( ) )
//  {
    // Retrieve definition of argument
//    Enode * arg_def = egraph.valDupMap1( formula->get1st( ) );
//    assert( arg_def );
//    vector< Enode * > clause;
//    clause.push_back( toggleLit( arg_def ) );
//#ifdef PRODUCE_PROOF
//    if ( config.produce_inter > 0 )
//      return solver.addSMTClause( clause
//	                        , partitions );
//#endif
//    return solver.addSMTClause( clause );
//  }

  return true;
}


void Tseitin::cnfizeAnd( PTRef and_term
                       , Lit v
#ifdef PRODUCE_PROOF
                       , const ipartitions_t partitions
#endif
                       )
{
//  assert( list );
//  assert( list->isList( ) );
    if (v == lit_Undef) {
        for (int i = 0; i < ptstore[and_term].size(); i++) {
            PTRef arg = ptstore[and_term][i];
            vec<Lit> little_clause;
            little_clause.push(findLit(arg));
#ifdef PRODUCE_PROOF
        if ( config.produce_inter > 0 )
            solver.addSMTClause( little_clause, partitions );
        else
#endif
            solver.addSMTClause( little_clause );        // Adds a little clause to the solver
        }
    }
    else {
        //
        // ( a_0 & ... & a_{n-1} )
        //
        // <=>
        //
        // aux = ( -aux | a_0 ) & ... & ( -aux | a_{n-1} ) & ( aux & -a_0 & ... & -a_{n-1} )
        //
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
}

void Tseitin::cnfizeOr( PTRef or_term
                      , Lit   v
#ifdef PRODUCE_PROOF
                      , const ipartitions_t partitions
#endif
                      )
{
//  assert( list );
//  assert( list->isList( ) );
    if (v == lit_Undef) {
        vec<Lit> big_clause;
        for (int i = 0; i < ptstore[or_term].size(); i++)
            big_clause.push(findLit(ptstore[or_term][i]));
#ifdef PRODUCE_PROOF
        if ( config.produce_inter > 0 )
            solver.addSMTClause( big_clause, partitions );
        else
#endif
            solver.addSMTClause(big_clause);
    }
    else {
        //
        // ( a_0 | ... | a_{n-1} )
        //
        // <=>
        //
        // aux = ( aux | -a_0 ) & ... & ( aux | -a_{n-1} ) & ( -aux | a_0 | ... | a_{n-1} )
        //
        vec<Lit>    little_clause;
        vec<Lit>    big_clause;
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
}

void Tseitin::cnfizeXor(PTRef xor_term
                       , Lit v
#ifdef PRODUCE_PROOF
                       , const ipartitions_t partitions
#endif
                       )
{
    if (v == lit_Undef) {
        Lit arg0 = findLit(ptstore[xor_term][0]);
        Lit arg1 = findLit(ptstore[xor_term][1]);

        vec<Lit> clause;

        clause.push(arg0);
        clause.push(arg1);
#ifdef PRODUCE_PROOF
        if ( config.produce_inter > 0 )
            solver.addSMTClause(clause, partitions);
        else
#endif
            solver.addSMTClause(clause);

        clause.pop();
        clause.pop();

        clause.push(~arg0);
        clause.push(~arg1);
#ifdef PRODUCE_PROOF
        if ( config.produce_inter > 0 )
            solver.addSMTClause(clause, partitions);
        else
#endif
        solver.addSMTClause(clause);
    }
    else {
        //
        // ( a_0 xor a_1 )
        //
        // <=>
        //
        // aux = ( -aux | a_0  | a_1 ) & ( -aux | -a_0 | -a_1 ) &
        //       (  aux | -a_0 | a_1 ) & (  aux |  a_0 | -a_1 )
        //
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
}

void Tseitin::cnfizeIff( PTRef eq_term
                       , Lit v
#ifdef PRODUCE_PROOF
                       , const ipartitions_t partitions
#endif
                       )
{
    if (v == lit_Undef) {
        Lit arg0 = findLit(ptstore[eq_term][0]);
        Lit arg1 = findLit(ptstore[eq_term][1]);

        vec<Lit> clause;

        clause.push( arg0);
        clause.push(~arg1);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            solver.addSMTClause(clause, partitions);
        else
#endif
            solver.addSMTClause(clause);

        clause.pop();
        clause.pop();

        clause.push(~arg0);
        clause.push( arg1);
#ifdef PRODUCE_PROOF
        if (config.produce_inter > 0)
            solver.addSMTClause(clause, partitions);
        else
#endif
            solver.addSMTClause(clause);
    }
    else {
        //
        // ( a_0 <-> a_1 )
        //
        // <=>
        //
        // aux = ( -aux |  a_0 | -a_1 ) & ( -aux | -a_0 |  a_1 ) &
        //       (  aux |  a_0 |  a_1 ) & (  aux | -a_0 | -a_1 )
        //
        assert(ptstore[eq_term].size() == 2);
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

