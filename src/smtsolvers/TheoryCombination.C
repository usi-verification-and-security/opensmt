/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso

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

#include "SimpSMTSolver.h"

/*
inline bool isArithmeticOp( Enode * e )
{
  if ( e->isPlus    ( ) 
    || e->isUminus  ( )
    || e->isTimes   ( )
    || e->isLeq     ( ) 
    || e->isVar     ( ) 
    || ( e->isConstant( ) && !e->isTrue( ) && !e->isFalse( ) ) )
    return true;

  return false;
}

inline bool isUFOp( Enode * e )
{
  if ( e->isUf       ( ) 
    || e->isUp       ( ) 
    || e->isDistinct ( ) 
    || e->isVar      ( ) 
    || ( e->isConstant( ) && !e->isTrue( ) && !e->isFalse( ) ) )
    return true;

  return false;
}

void SimpSMTSolver::gatherInterfaceTerms( Enode * e )
{
  assert( config.sat_lazy_dtc != 0 );
  assert( config.logic == QF_UFIDL
       || config.logic == QF_UFLRA );

  assert( e );
  vector< Enode * > unprocessed_enodes;
  egraph.initDup1( );

  unprocessed_enodes.push_back( e );
  //
  // Visit the DAG of the term from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    // 
    // Skip if the node has already been processed before
    //
    if ( egraph.isDup1( enode ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( ) ; 
	  arg_list != egraph.enil ; 
	  arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !egraph.isDup1( arg ) )
      {
	unprocessed_enodes.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    unprocessed_enodes.pop_back( );                      
    //
    // At this point, every child has been processed
    //
    if ( isUFOp( enode ) )
    {
      // Retrieve arguments
      for ( Enode * arg_list = enode->getCdr( ) 
	  ; !arg_list->isEnil( ) 
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = arg_list->getCar( );
	if ( isArithmeticOp( arg ) )
	  if ( interface_terms_cache.insert( arg ).second )
	  {
	    interface_terms.push_back( arg );
	    cerr << "Added: " << arg << endl;
	  }
      }
    }
    else if ( isArithmeticOp( enode ) )
    {
      // Retrieve arguments
      for ( Enode * arg_list = enode->getCdr( ) 
	  ; !arg_list->isEnil( ) 
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = arg_list->getCar( );
	if ( isUFOp( arg ) )
	  if ( interface_terms_cache.insert( arg ).second )
	  {
	    interface_terms.push_back( arg );
	    cerr << "Added: " << arg << endl;
	  }
      }
    }

    assert( !egraph.isDup1( enode ) );
    egraph.storeDup1( enode );
  }

  egraph.doneDup1( );
}
*/

// Generates a bunch of eij, and return one
Var CoreSMTSolver::generateMoreEij( )
{
  Var ret = var_Undef;

  for ( int i = 0 
      ; i < (config.sat_lazy_dtc_burst < 0 ? 1 : config.sat_lazy_dtc_burst) 
      ; i ++ )
  {
    Var v = generateNextEij( );
    // Return if no more eij
    if ( v == var_Undef ) 
      return v;
    // Save return variable
    if ( i == 0 ) ret = v;
  }

  return ret;
}

Var CoreSMTSolver::generateNextEij( )
{
  if ( egraph.getInterfaceTermsNumber( ) == 0 )
    return var_Undef;

  assert( config.sat_lazy_dtc != 0 );
  Var v = var_Undef;
  lbool pol = l_Undef;
  while ( v == var_Undef )
  {
    // Already returned all the possible eij
    if ( next_it_i == egraph.getInterfaceTermsNumber( ) - 1 
      && next_it_j == egraph.getInterfaceTermsNumber( ) )
      return var_Undef;

    // Get terms
    // Enode * i = interface_terms[ next_it_i ];
    // Enode * j = interface_terms[ next_it_j ];
    Enode * i = egraph.getInterfaceTerm( next_it_i );
    Enode * j = egraph.getInterfaceTerm( next_it_j );
    // Increase counters
    next_it_j ++;
    if ( next_it_j == next_it_i ) next_it_j ++;
    // if ( next_it_j == static_cast< int >( interface_terms.size( ) ) )
    if ( next_it_j == egraph.getInterfaceTermsNumber( ) )
    {
      next_it_i ++; 
      next_it_j = next_it_i + 1;
    }
    // No need to create eij if both numbers,
    // it's either trivially true or false
    if ( i->isConstant( ) 
      && j->isConstant( ) )
      continue;

    assert( config.logic == QF_UFLRA
	 || config.logic == QF_UFIDL );

    //
    // Since arithmetic solvers do not 
    // understand equalities, produce
    // the splitted versions of equalities
    // and add linking clauses
    //
    Enode * eij = egraph.mkEq( egraph.cons( i, egraph.cons( j ) ) );
    // Skip as this interface equality already exists
    // as a theory atom, and so no need to generate it
    if ( atoms_seen.find( eij ) != atoms_seen.end( ) )
      continue;
#ifdef PRODUCE_PROOF
    if ( config.produce_inter != 0 
      && eij->getIPartitions( ) == 0 )	
    {
      eij->setIPartitions( i->getIPartitions( ) 
	                 & j->getIPartitions( ) );
      // Set explicitly ABmixed
      if ( eij->getIPartitions( ) == 0 )
	eij->setIPartitions( 1 );
    }
#endif

    if ( config.verbosity > 2 )
    {
      // cerr << "# CoreSMTSolver::Adding eij: " << eij << endl;
      cerr << "\rLazy DTC Progress: " 
	   << ( 100 * (float)next_it_i / (float)egraph.getInterfaceTermsNumber( ) ) 
	   << " %";
    }

    if ( eij->isTrue( ) || eij->isFalse( ) ) continue;
    // Canonize
    LAExpression la( eij );
    Enode * eij_can = la.toEnode( egraph );
    // Continue if already generated equality
    // if ( !interface_equalities.insert( eij_can ).second ) continue;
    if ( eij_can->isTrue( ) || eij_can->isFalse( ) ) continue;
    v = theory_handler->enodeToVar( eij );
    // Created one equality that is already assigned
    // Skip it
    if ( value( v ) != l_Undef )
    {
      v = var_Undef;
      continue;
    }
    // Get lhs and rhs
    Enode * lhs = eij_can->get1st( );
    Enode * rhs = eij_can->get2nd( );
    Enode * leq = egraph.mkLeq( egraph.cons( lhs, egraph.cons( rhs ) ) );
    // Canonize lhs
    LAExpression b( leq );
    leq = b.toEnode( egraph );
    // We need to color this guy ...
#ifdef PRODUCE_PROOF
    if ( config.produce_inter != 0 
      && atoms_seen.find( leq ) == atoms_seen.end( ) 
      && leq->getIPartitions( ) == 0 )	
    {
      leq->setIPartitions( lhs->getIPartitions( ) 
	                 & rhs->getIPartitions( ) );
      // Set ABmixed
      if ( leq->getIPartitions( ) == 0 )
	leq->setIPartitions( 1 );
    }
#endif
    // Canonize rhs
    Enode * geq = egraph.mkGeq( egraph.cons( lhs, egraph.cons( rhs ) ) );
    LAExpression c( geq );
    geq = c.toEnode( egraph );
    // We need to color this guy ...
#ifdef PRODUCE_PROOF
    if ( config.produce_inter != 0 
      && atoms_seen.find( geq ) == atoms_seen.end( ) 
      && geq->getIPartitions( ) == 0 )	
    {
      geq->setIPartitions( lhs->getIPartitions( ) 
	                 & rhs->getIPartitions( ) );
      // Set ABmixed
      if ( geq->getIPartitions( ) == 0 )
	geq->setIPartitions( 1 );
    }
#endif
    // Add clause ( !x=y v x<=y )
    vector< Enode * > clause;
    clause.push_back( egraph.mkNot( egraph.cons( eij ) ) );
    clause.push_back( leq );
    assert( !leq->isTrue( ) );
    assert( !leq->isFalse( ) );
#ifdef PRODUCE_PROOF
    addSMTAxiomClause( clause
	             , computeAxiomInterp( clause ) );
#else
    addSMTAxiomClause( clause );
#endif
    // Add clause ( !x=y v x>=y )
    clause.pop_back( );
    clause.push_back( geq );
    assert( !leq->isTrue( ) );
    assert( !leq->isFalse( ) );
#ifdef PRODUCE_PROOF
    addSMTAxiomClause( clause
	             , computeAxiomInterp( clause ) );
#else
    addSMTAxiomClause( clause );
#endif
    // Add clause ( x=y v !x>=y v !x<=y )
    clause.clear( );
    clause.push_back( eij );
    clause.push_back( egraph.mkNot( egraph.cons( leq ) ) );
    clause.push_back( egraph.mkNot( egraph.cons( geq ) ) );
#ifdef PRODUCE_PROOF
    addSMTAxiomClause( clause
	             , computeAxiomInterp( clause ) );
#else
    addSMTAxiomClause( clause );
#endif

    pol = theory_handler->evaluate( eij );
    if ( pol == l_Undef ) pol = theory_handler->evaluate( leq );
    if ( pol == l_Undef ) pol = theory_handler->evaluate( geq );
    /*
    else
    {
      Enode * eij = egraph.mkEq( egraph.cons( i, egraph.cons( j ) ) );
#ifdef PRODUCE_PROOF
      if ( config.produce_inter != 0 )
      {
        eij->setIPartitions( i->getIPartitions( ) 
                           & j->getIPartitions( ) );
        // Set ABmixed
        if ( eij->getIPartitions( ) == 0 )
          eij->setIPartitions( 1 );
      }
#endif
      // Continue if already generated equality
      if ( !interface_equalities.insert( eij ).second ) continue;
      if ( eij->isTrue( ) || eij->isFalse( ) ) continue;
      // Add new atom and get variable
      v = theory_handler->enodeToVar( eij );
      // Initialize congruence data structure
      egraph.initializeCong( eij );
    }
    */
  }
#ifdef STATISTICS
  ie_generated ++;
#endif
  assert( v != var_Undef );
  assert( polarity.size( ) > v );
  // Assign to false first. We merge the least possible
  // Alternatively we can merge the most, or 
  polarity[ v ] = ( pol == l_True 
                    ? false 
		    : ( pol == l_False 
		        ? true 
			: true ) );

  return v;
}

#ifdef PRODUCE_PROOF
//
// e belongs either to one partition or
// to several consecutive. We set the interpolant
// to be TTTTFFFF where the changing point
// is the first partition e belongs to. Notice
// that this clause contains only e and its variations
// so, whatever is the color for e is the color for the
// clause
//
Enode * CoreSMTSolver::computeAxiomInterp( vector< Enode * > & clause )
{
  ipartitions_t clause_parts = clause[ 0 ]->isNot( )
                             ? clause[ 0 ]->get1st( )->getIPartitions( ) 
			     : clause[ 0 ]->getIPartitions( )
			     ;
  for ( size_t i = 1 ; i < clause.size( ) ; i ++ )
  {
    clause_parts &= clause[ i ]->isNot( ) 
                  ? clause[ i ]->get1st( )->getIPartitions( )
		  : clause[ i ]->getIPartitions( )
		  ;
  }
  list< Enode * > in_list;
  // Set the mask as 1..10
  ipartitions_t mask = 1;
  mask = ~mask;
  Enode * curr_int = egraph.mkTrue( );
  // Scan the various partitions
  for( unsigned in = 1 ; in < egraph.getNofPartitions( ) ; in ++ )
  {
    // mask &= ~SETBIT( in );
    clrbit( mask, in );

    // McMillan algo, set AB to B
    if ( config.proof_set_inter_algo == 0 )
    {
      if ( isAstrict( clause_parts, mask ) )
	curr_int = egraph.mkFalse( );
      else 
	curr_int = egraph.mkTrue( );
    }
    // McMillan' algo, set AB to A
    else if ( config.proof_set_inter_algo == 2 )
    {
      if ( isBstrict( clause_parts, mask ) )
	curr_int = egraph.mkTrue( );
      else
	curr_int = egraph.mkFalse( );
    }
    // For pudlak we don't care ...
    else if ( config.proof_set_inter_algo == 1 
	   && isAlocal( clause_parts, mask ) )
      curr_int = egraph.mkFalse( );

    in_list.push_front( curr_int ); 
  }
  return egraph.cons( in_list );
}
#endif
