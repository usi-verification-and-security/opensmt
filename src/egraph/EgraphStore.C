/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008-2010, Roberto Bruttomesso

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

#include "Egraph.h"
#include "LA.h"
#include "BVNormalize.h"
#include "BVBooleanize.h"
#include "SimpSMTSolver.h"

void Egraph::initializeStore( )
{
  //
  // Reserve room for at least 65536 nodes
  //
  id_to_enode .reserve( 65536 );

  assert( config.logic != UNDEF );

  // 
  // Create default sorts 
  //
//  Snode * sbool1  = sort_store.mkBool( );
//  Snode * sparA1  = sort_store.mkPara( "_A_" );
//  Snode * sparB1  = sort_store.mkPara( "_B_" );
//  sarith1 = config.logic == QF_LRA
//         || config.logic == QF_RDL
//	  ? sort_store.mkReal( ) 
//	  : sort_store.mkInt ( );
//  Snode * sarray1 = sort_store.mkVar( new IdNode( "Array", NULL ) );
  //
  // Some useful shortcuts
  //
//  Snode * sbool1_list  = sort_store.cons( sbool1 );
//  Snode * sbool2_list  = sort_store.cons( sbool1, sbool1_list );
//
//  Snode * sbool2 = sort_store.mkDot( sbool2_list );
//
//  Snode * sparA2 = sort_store.mkDot( sort_store.cons( sparA1
//                                   , sort_store.cons( sparA1 ) ) );
//
//  Snode * sbool_parA2 = sort_store.mkDot( sort_store.cons( sbool1
//                                        , sort_store.cons( sparA1
//                                        , sort_store.cons( sparA1 ) ) ) );
  //
  // Allocates SMTLIB predefined symbols
  //
  newSymbol( "true"  , NULL, sbool1 ); assert( ENODE_ID_TRUE    == id_to_enode.size( ) - 1 );
  newSymbol( "false" , NULL, sbool1 ); assert( ENODE_ID_FALSE   == id_to_enode.size( ) - 1 );
  //
  // Core
  //
  newSymbol( "not"     , sbool1     , sbool1 ); assert( ENODE_ID_NOT      == id_to_enode.size( ) - 1 );
  newSymbol( "=>"      , sbool2     , sbool1 ); assert( ENODE_ID_IMPLIES  == id_to_enode.size( ) - 1 );
  newSymbol( "and"     , sbool2     , sbool1 ); assert( ENODE_ID_AND      == id_to_enode.size( ) - 1 );
  newSymbol( "or"      , sbool2     , sbool1 ); assert( ENODE_ID_OR       == id_to_enode.size( ) - 1 );
  newSymbol( "xor"     , sbool2     , sbool1 ); assert( ENODE_ID_XOR      == id_to_enode.size( ) - 1 );
  newSymbol( "="       , sparA2     , sbool1 ); assert( ENODE_ID_EQ       == id_to_enode.size( ) - 1 );
  newSymbol( "ite"     , sbool_parA2, sparA1 ); assert( ENODE_ID_ITE      == id_to_enode.size( ) - 1 );
  newSymbol( "distinct", sparA2     , sbool1 ); assert( ENODE_ID_DISTINCT == id_to_enode.size( ) - 1 );
  //
  // Arithmetic predefined operators and predicates
  //
  // TODO: from here down this has to be changed to something 
  //       that parses the signature ...
  //
  // Some useful shortcuts
  //
//  Snode * sarith1_list = sort_store.cons( sarith1 );
//  Snode * sarith2_list = sort_store.cons( sarith1, sarith1_list );
//  Snode * sarith2      = sort_store.mkDot( sarith2_list );

//  newSymbol( "+"       , sarith2, sarith1 ); assert( ENODE_ID_PLUS   == id_to_enode.size( ) - 1 );
//  newSymbol( "-"       , sarith2, sarith1 ); assert( ENODE_ID_MINUS  == id_to_enode.size( ) - 1 );
//  newSymbol( "-"       , sarith1, sarith1 ); assert( ENODE_ID_UMINUS == id_to_enode.size( ) - 1 );
//  newSymbol( "*"       , sarith2, sarith1 ); assert( ENODE_ID_TIMES  == id_to_enode.size( ) - 1 );
//  newSymbol( "/"       , sarith2, sarith1 ); assert( ENODE_ID_DIV    == id_to_enode.size( ) - 1 );
//  newSymbol( "<="      , sarith2, sbool1 );  assert( ENODE_ID_LEQ    == id_to_enode.size( ) - 1 );
//  newSymbol( ">="      , sarith2, sbool1 );  assert( ENODE_ID_GEQ    == id_to_enode.size( ) - 1 );
//  newSymbol( "<"       , sarith2, sbool1 );  assert( ENODE_ID_LT     == id_to_enode.size( ) - 1 );
//  newSymbol( ">"       , sarith2, sbool1 );  assert( ENODE_ID_GT     == id_to_enode.size( ) - 1 );

//  Snode * sarray_parA_parB = sort_store.mkDot( sort_store.cons( sarray1
//                                             , sort_store.cons( sparA1
//                                             , sort_store.cons( sparB1 ) ) ) );
//
//  Snode * sarray_parA_parB__parA = sort_store.mkDot( sort_store.cons( sarray_parA_parB
//	                                           , sort_store.cons( sparA1 ) ) );
//
//  Snode * sarray_parA_parB__parA_parB = sort_store.mkDot( sort_store.cons( sarray_parA_parB
//	                                                , sort_store.cons( sparA1
//							, sort_store.cons( sparB1 ) ) ) );

//  newSymbol( "store"   , sarray_parA_parB__parA_parB, sarray_parA_parB ); assert( ENODE_ID_STORE  == id_to_enode.size( ) - 1 );
//  newSymbol( "select"  , sarray_parA_parB__parA, sparB1 );                assert( ENODE_ID_SELECT == id_to_enode.size( ) - 1 );
  //
  // Cost theory symbols
  //
//  Snode * scost1 = sort_store.mkCost( );
//  Snode * snum1  = sort_store.mkInt ( );

//  Snode * sct_incur = sort_store.mkDot( sort_store.cons( scost1
//                                      , sort_store.cons( snum1
//		                      , sort_store.cons( snum1 ) ) ) );
//
//  Snode * sct_bound = sort_store.mkDot( sort_store.cons( scost1
//		                      , sort_store.cons( snum1 ) ) );
//
//  newSymbol( "incur", sct_incur, sbool1 ); assert( ENODE_ID_CTINCUR == id_to_enode.size( ) - 1 );
//  newSymbol( "bound", sct_bound, sbool1 ); assert( ENODE_ID_CTBOUND == id_to_enode.size( ) - 1 );

//  Snode * sarray_parA_parB_array_parA_parB = sort_store.mkDot( sort_store.cons( sarray_parA_parB
//	                                                     , sort_store.cons( sarray_parA_parB ) ) );
//
  newSymbol( "diff", sarray_parA_parB_array_parA_parB, sparA1 ); assert( ENODE_ID_DIFF == id_to_enode.size( ) - 1 );

  newSymbol( "fake_interp", NULL, sbool1 ); assert( ENODE_ID_FAKE_INTERP == id_to_enode.size( ) - 1 );
  //
  // Set top node to empty
  //
  top = NULL;
  //
  // Allocate true and false
  //
  etrue  = allocTrue ( );
  efalse = allocFalse( );
  //
  // Does not have ites (yet)
  //
  has_ites = false;
  //
  // Inserts true and false in signature table
  //
  insertSigTab( etrue );
  insertSigTab( efalse );
}

//
// Allocates true
//
Enode * Egraph::allocTrue ( )
{
  Enode * res = cons( id_to_enode[ ENODE_ID_TRUE ] );
  assert( res );
  assert( res->isTerm( ) );
  res->allocCongData( );
  res->setConstant( res );
#ifdef PRODUCE_PROOF
  // Not using config.produce_inter flag as not yet set
  // True/False are shared over all partitions
  ipartitions_t mask = -1;
  res->setIPartitions( mask );
#endif
  return res;
}

//
// Allocates false
//
Enode * Egraph::allocFalse ( )
{
  Enode * res = cons( id_to_enode[ ENODE_ID_FALSE ] );
  assert( res );
  assert( res->isTerm( ) );
  res->allocCongData( );
  res->setConstant( res );
#ifdef PRODUCE_PROOF
  // Not using config.produce_inter flag as not yet set
  // True/False are shared over all partitions
  ipartitions_t mask = -1;
  res->setIPartitions( mask );
#endif
  return res;
}

//
// Inserts a number
//
Enode * Egraph::insertNumber( Enode * n )
{
  assert( n->isNumb( ) );
  pair< map< string, Enode * >::iterator, bool > res = name_to_number.insert( make_pair( n->getName( ), n ) );
  // Number has been inserted
  if ( res.second )
  {
    // TODO: should make this incremental as well ? not clear
    // undo_stack_term.push_back( n );
    // undo_stack_oper.push_back( NUMB );
    id_to_enode .push_back( n );
    assert( n->getId( ) == (enodeid_t)id_to_enode.size( ) - 1 );
    return n;
  }
  // Number was already there, get rid of n
  delete n;
  // Return the old one
  return res.first->second;
}

//
// Inserts a symbol
//
void Egraph::insertSymbol( Enode * s )
{
  assert( s );
  assert( s->isSymb( ) );
  // Consistency for id
  assert( (enodeid_t)id_to_enode.size( ) == s->getId( ) );
  // Symbol is not there
  assert( name_to_symbol.find( s->getNameFull( ) ) == name_to_symbol.end( ) );
  // Insert Symbol
  name_to_symbol[ s->getNameFull( ) ] = s;
  id_to_enode .push_back( s );
}

//
// Removes a symbol
//
void Egraph::removeSymbol( Enode * s )
{
  assert( s->isSymb( ) );
  assert( config.incremental );
  map< string, Enode * >::iterator it = name_to_symbol.find( s->getName( ) );
  assert( it != name_to_symbol.end( ) );
  assert( it->second == s );
  name_to_symbol.erase( it );
  id_to_enode[ s->getId( ) ] = NULL;
  delete s;
}

//
// Inserts a number
//
void Egraph::removeNumber( Enode * n )
{
  assert( n->isNumb( ) );
  assert( config.incremental );
  map< string, Enode * >::iterator it = name_to_number.find( n->getName( ) );
  assert( it != name_to_number.end( ) );
  assert( it->second == n );
  name_to_number.erase( it );
  assert( n->getId( ) == (enodeid_t)id_to_enode.size( ) - 1 );
  id_to_enode.pop_back( );
  delete n;
}

//
// Retrieves a symbol from the name
//
Enode * Egraph::lookupSymbol( const char * name )
{
  assert( name );
  map< string, Enode * >::iterator it = name_to_symbol.find( name );
  if ( it == name_to_symbol.end( ) ) return NULL;
  return it->second;
}

//
// Retrieves a define
//
Enode * Egraph::lookupDefine( const char * name )
{
  assert( name );
  map< string, Enode * >::iterator it = name_to_define.find( name );
  if ( it == name_to_define.end( ) ) return NULL;
  return it->second;
}

//
// Store a define
//
void Egraph::insertDefine( const char * n, Enode * d )
{
  assert( d );
  assert( n );
  assert( d->isDef( ) );
  assert( (enodeid_t)id_to_enode.size( ) == d->getId( ) );
  assert( name_to_define.find( n ) == name_to_define.end( ) );
  name_to_define[ n ] = d;
  id_to_enode.push_back( d );
}

//
// Insert into signature table possibly creating a new node
//
Enode * Egraph::insertSigTab ( const enodeid_t id, Enode * car, Enode * cdr )
{
  assert( car == car->getRoot( ) );
  assert( cdr == cdr->getRoot( ) );

#ifdef BUILD_64
  enodeid_pair_t sig = encode( car->getCid( ), cdr->getCid( ) );
#else
  const Pair( enodeid_t ) sig = make_pair( car->getCid( ), cdr->getCid( ) );
#endif
  Enode * res = sig_tab.lookup( sig );

  if ( res == NULL )
  {
    Enode * e = new Enode( id, car, cdr );
    sig_tab.insert( e );
    return e;
  }

  return res;
}

//
// Insert into Store
//
Enode * Egraph::insertStore( const enodeid_t id, Enode * car, Enode * cdr )
{
  static Enode* new_enode = NULL;

  if (new_enode == NULL)
      new_enode = new Enode( id, car, cdr );
  else {
      new_enode->~Enode();
      new_enode = new(new_enode) Enode( id, car, cdr);
  }

  Enode * x = store.insert( new_enode );
  // Node already there
  if ( x != new_enode ) return x;
  // Insertion done
  new_enode = NULL;
  return x;
}

//
// Remove from Store
//
void Egraph::removeStore( Enode * e )
{
  assert( e );
  store.remove( e );
}

//
// Retrieve element from signature table
//
Enode * Egraph::lookupSigTab ( Enode * e )
{
  Enode * res = sig_tab.lookup( e->getSig( ) );
  return res;
}

//
// Adds element to signature table
//
Enode * Egraph::insertSigTab ( Enode * e )
{
  sig_tab.insert( e );
  return e;
}

//
// Remove element from signature table
//
void Egraph::removeSigTab ( Enode * e )
{
  assert( lookupSigTab( e ) );
  sig_tab.erase( e );
}

//
// Copy list into a new one whose elements are retrieved from the cache
//

Enode * Egraph::copyEnodeEtypeListWithCache( Enode * l, bool map2 )
{
  assert(  map2 || active_dup_map1 );
  assert( !map2 || active_dup_map2 );

  list< Enode * > new_args;
  for ( Enode * arg = l ; !arg->isEnil( ) ; arg = arg->getCdr( ) )
  {
    new_args.push_front( map2
		       ? valDupMap2( arg->getCar( ) )
		       : valDupMap1( arg->getCar( ) )
		       );
  }

  Enode * res = cons( new_args );
  return res;
}

//
// Create a new term of the same kind but using info in the cache and
// also performs some simplifications
//
Enode * Egraph::copyEnodeEtypeTermWithCache( Enode * term, bool map2 )
{
  assert(  map2 || active_dup_map1 );
  assert( !map2 || active_dup_map2 );
  Enode * ll = copyEnodeEtypeListWithCache( term->getCdr( ), map2 );
  assert( ll->isList( ) );
  //
  // Case
  //
  if ( term->isAnd        ( ) ) return mkAnd       ( ll );
  if ( term->isOr         ( ) ) return mkOr        ( ll );
  if ( term->isNot        ( ) ) return mkNot       ( ll );
  if ( term->isImplies    ( ) ) return mkImplies   ( ll );
  if ( term->isXor        ( ) ) return mkXor       ( ll );
  if ( term->isEq         ( ) ) return mkEq        ( ll );
  if ( term->isLeq        ( ) ) return mkLeq       ( ll );
  if ( term->isPlus       ( ) ) return mkPlus      ( ll );
  if ( term->isTimes      ( ) ) return mkTimes     ( ll );
  if ( term->isDiv        ( ) ) return mkDiv       ( ll );
  if ( term->isDistinct   ( ) ) return mkDistinct  ( ll );

  if ( ll->getArity( ) == 3 )
  {
    Enode * i = ll->getCar( );
    Enode * t = ll->getCdr( )->getCar( );
    Enode * e = ll->getCdr( )->getCdr( )->getCar( );

    if ( term->isIte        ( ) ) return mkIte        ( i, t, e );
  }

  if ( term->isVar( ) || term->isConstant( ) )
    return term;

  //
  // Enable if you want to make sure that your case is handled
  //
  // error( "Please add a case for ", term->getCar( ) );

  Enode * new_term = cons( term->getCar( ), ll );
  return new_term;
}

//
// FIXME: This is a little bit counter intuitive
// The list given is now in reverse order w.r.t.
// the returned one, they should insted be the
// same, more logical. But that implies that we
// have to modify other parts of the code, so
// be careful
//
Enode * Egraph::cons( list< Enode * > & args )
{
  Enode * elist = const_cast< Enode * >( enil );

  for ( list< Enode * >::iterator it = args.begin( )
      ; it != args.end( )
      ; it ++ )
    elist = cons( *it, elist );

  return elist;
}

Enode * Egraph::cons( Enode ** args, unsigned count )
{
  Enode * elist = const_cast< Enode * >( enil );

  for ( unsigned i = count; i > 0; --i) {
    elist = cons( args[i-1], elist );
  }
  return elist;
}

//
// Creates a new term and its correspondent modulo equivalence
//
Enode * Egraph::cons( Enode * car, Enode * cdr )
{
  assert( car );
  assert( cdr );
  assert( car->isTerm( ) || car->isSymb( ) || car->isNumb( ) );
  assert( cdr->isList( ) );
  Enode * e = NULL;
  // Create and insert a new enode if necessary
  e = insertStore( id_to_enode.size( ), car, cdr );
  assert( e );
  // The node was there already. Return it
  if ( (enodeid_t)id_to_enode.size( ) != e->getId( ) )
    return e;

  /*
   * Had to disable because of problems
   * connected with incrementality of
   * congruence closure. It seems that a node
   * after it is removed still survive in the
   * signature tab, causing obvious inconsistencies
   * in the invariants
   *
   * TO BE CLARIFIED !
   *
  if ( config.incremental )
  {
    // Save Backtrack information
    undo_stack_term.push_back( e );
    undo_stack_oper.push_back( INSERT_STORE );
  }
  */

#ifdef PRODUCE_PROOF
  // Set the color
  if (  automatic_coloring 
    &&  e->isTerm( )           // Only terms needs coloring
    &&  e->getArity( ) > 0     // of arity > 0
    && !e->hasSortBool( )      // that don't have sort boolean
    )    
  {
    assert( e->getIPartitions( ) == 0 );
    ipartitions_t parts = 0;
    // If it's UF, it has it's own partitions
    if ( e->isUf( ) )
      parts = e->getCar( )->getIPartitions( );
    for ( Enode * arg_list = e->getCdr( )
        ; !arg_list->isEnil( )	
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->getIPartitions( ) != 0 );
      if ( parts == 0 )
	parts = arg->getIPartitions( );
      else
	parts &= arg->getIPartitions( );
    }
    // cerr << "Assigning partitions: " << parts << " to " << e << endl;
    // It's ab-mixed
    if( parts == 0 )
      parts = 1;
    // This is the only place allowed to use this function
    e->setIPartitions( parts );
  }
#endif

  // We keep the created enode
  id_to_enode.push_back( e );
  return e;
}

//
// Create a variable
//
Enode * Egraph::mkVar( const char * name, bool model_var )
{
  Enode * e = lookupSymbol( name );
  // Not a variable, is it a define ?
  if ( e == NULL ) 
  {
    e = lookupDefine( name );
    // Not a define, abort
    if ( e == NULL )
      opensmt_error2( "undeclared identifier ", name );
    assert( e->isDef( ) );
    // It's a define, return itss definition
    return e->getDef( );
  }
  // It's a variable
  Enode * res = cons( e );
  if ( model_var )
    variables.insert( res );
  return res;
}

Enode * Egraph::mkNum( const char * value )
{
  assert( value );
  Enode * new_enode = new Enode( id_to_enode.size( )
			       , value
			       , ETYPE_NUMB
			       , NULL
                               , sarith1 );

  assert( new_enode );
  Enode * res = insertNumber( new_enode );
  res = cons( res );
#ifdef PRODUCE_PROOF
  if ( config.produce_inter != 0
    && res->getIPartitions( ) == 0 )
  {
    // Numbers are shared over all partitions
    ipartitions_t mask = 0;
    mask = ~mask;
    res->setIPartitions( mask );
  }
#endif
  return res;
}

Enode * Egraph::mkNum( const Real & real_value )
{
#if FAST_RATIONALS
  return mkNum( const_cast< char * >(real_value.get_str( ).c_str( )) );
#elif USE_GMP
  return mkNum( const_cast< char * >(real_value.get_str( ).c_str( )) );
#else
  char buf[ 128 ];
  sprintf( buf, "%lf", real_value );
  return mkNum( buf );
#endif
}

Enode * Egraph::mkNum( const char * num, const char * den )
{
  string s = (string)num + "/" + (string)den;

#if FAST_RATIONALS
  Real real_value( s.c_str() );
  return mkNum( const_cast< char * >(real_value.get_str( ).c_str( )) );
#else
  Real num_d = atof( num );
  Real den_d = atof( den );
  Real value = num_d / den_d;
  return mkNum( value );
#endif
}

Enode * Egraph::mkFun( const char * name, Enode * args )
{
  assert( args->isList( ) );
  //
  // Retrieve sort from arguments
  //
  stringstream ss;
  ss << name;
  for ( Enode * l = args ; !l->isEnil( ) ; l = l->getCdr( ) )
  {
    ss << " ";  
    ss << l->getCar( )->getRetSort( )->toString();
  }

  Enode * e = lookupSymbol( ss.str( ).c_str( ) );
  if ( e == NULL ) opensmt_error2( "undeclared function symbol ", ss.str( ).c_str( ) );

  Enode * ret = cons( e, args ); 
  return ret;
}

/****************************************************************
 * New interface for creating a new symbol
 */

Enode * Egraph::newSymbol( const char * name
                         , list<Sort*>& args
                         , Sort& retv
                         , uint64_t )           // unused
{
  stringstream ss;
  ss << name;
  ss << " ";
  for (std::list<Sort*>::iterator it = args.begin(); it != args.end(); it++)
    ss << (**it).toString() << " ";
  ss << std::endl;


  if ( lookupSymbol( ss.str( ).c_str( ) ) != NULL )
    opensmt_error2( "symbol already declared ", ss.str( ).c_str( ) );

  Enode * new_enode = new Enode( id_to_enode.size( )
			       , ss.str( ).c_str( )
                               , ETYPE_SYMB
			       , args
                               , retv );

  insertSymbol( new_enode );	           
  assert( lookupSymbol( ss.str( ).c_str( ) ) == new_enode );
  return new_enode;
}
//
// Creates a new symbol. Name must be new
//
Enode * Egraph::newSymbol( const char * name
                         , Sort * args 
                         , Sort * retv 
			 , uint64_t )            // parameter for properties, not used now
{
  assert( retv );
  assert( retv->isTerm( ) );
  assert( args == NULL || args->isTerm( ) );

  stringstream ss;
  ss << name;
  if ( args ) ss << " " << args->getArgs( );

  if ( lookupSymbol( ss.str( ).c_str( ) ) != NULL )
    opensmt_error2( "symbol already declared ", ss.str( ).c_str( ) );

  Enode * new_enode = new Enode( id_to_enode.size( )
			       , ss.str( ).c_str( )
                               , ETYPE_SYMB
			       , args
                               , retv );

  insertSymbol( new_enode );	           
  assert( lookupSymbol( ss.str( ).c_str( ) ) == new_enode );
  return new_enode;
}

Enode * Egraph::getDefine( const char * name )
{
  Enode * e = lookupDefine( name );
  assert( e );
  assert( e->getCar( ) != NULL );
  return e->getCar( );
}

void Egraph::mkDefine( const char * name, Enode * def )
{
  Enode * e = lookupDefine( name );
  if( e == NULL )
  {
    Enode * new_enode = new Enode( id_to_enode.size( ), def );
    insertDefine( name, new_enode );
  }
  else
  {
    // This symbol has been declared before. We just
    // replace its definition with this new one
    e->setDef( def );
  }
}

Enode * Egraph::mkSelect( Enode * a, Enode * i )
{
  //
  // Check arguments: select is applied to an array expression and
  // an index expression remember the possibility of having ite
  // expressions as arguments
  //
  assert( a );
  assert( i );
  Sort * as = a->getRetSort( );
  Sort * is = i->getRetSort( );
  Sort * es = as->get3rd( );
  assert( !as->getCar( )->isPara( ) );
  assert( !is->getCar( )->isPara( ) );
  assert( !es->getCar( )->isPara( ) );
  assert( as->get2nd( ) == is );
  assert( as->get3rd( ) == es );
  //
  // Select has a parametric sort. We make sure that
  // a store with current sorts exists, in case we
  // create it
  //
  stringstream ss;
  ss << "select " << as << " " << is;
  Enode * symb = lookupSymbol( ss.str( ).c_str( ) );
  if ( symb == NULL )
  {
    Snode * saie_i = sort_store.mkDot( sort_store.cons( as
                                 , sort_store.cons( is ) ) );
    symb = newSymbol( "select", saie_i, es );

    sarray = as;
    sindex = as->get2nd( );
    selem  = as->get3rd( );
  }

  Enode * newSel = cons( symb, cons( a, cons( i ) ) );
  return newSel;
}

Enode * Egraph::mkStore( Enode * a, Enode * i, Enode * e )
{
  //
  // check arguments: store is applied to an array expression,
  // an index expression, and an element expression
  // remember the possibility of having ite expressions as arguments
  //
  assert( a );
  assert( i );
  assert( e );
  Snode * as = a->getRetSort( );
  Snode * is = i->getRetSort( );
  Snode * es = e->getRetSort( );
  assert( !as->getCar( )->isPara( ) );
  assert( !is->getCar( )->isPara( ) );
  assert( !es->getCar( )->isPara( ) );
  assert( as->get2nd( ) == is );
  assert( as->get3rd( ) == es );
  //
  // Store has a parametric sort. We make sure that
  // a store with current sorts exists, in case we
  // create it
  //
  stringstream ss;
  ss << "store " << as << " " << is << " " << es;
  Enode * symb = lookupSymbol( ss.str( ).c_str( ) );
  if ( symb == NULL )
  {
    Snode * saie_i_e = sort_store.mkDot( sort_store.cons( as
	                               , sort_store.cons( is
				       , sort_store.cons( es ) ) ) );
    symb = newSymbol( "store", saie_i_e, as ); 

    sarray = as;
    sindex = as->get2nd( );
    selem  = as->get3rd( );
  }

  Enode * newSto = cons( symb, cons( a, cons( i, cons( e ) ) ) );

  return newSto;
}

Enode * Egraph::mkDiff( Enode * a, Enode * b )
{
  //
  // check arguments: store is applied to an array expression,
  // an index expression, and an element expression
  // remember the possibility of having ite expressions as arguments
  //
  assert( a );
  assert( b );
  //
  // Diff is commutative
  // Swap if necessary
  //
  if ( a->getId( ) > b->getId( ) )
  {
    Enode * tmp = a;
    a = b;
    b = tmp;
  }
  Snode * as = a->getRetSort( );
  Snode * bs = b->getRetSort( );
  assert( as == bs );
  assert( !as->getCar( )->isPara( ) );
  assert( !bs->getCar( )->isPara( ) );
  //
  // Store has a parametric sort. We make sure that
  // a store with current sorts exists, in case we
  // create it
  //
  stringstream ss;
  ss << "diff " << as << " " << bs;
  Enode * symb = lookupSymbol( ss.str( ).c_str( ) );
  if ( symb == NULL )
  {
    Snode * is = as->get2nd( );
    Snode * sab = sort_store.mkDot( sort_store.cons( as
	                          , sort_store.cons( bs ) ) );

    symb = newSymbol( "diff", sab, is ); 

    sarray = as;
    sindex = as->get2nd( );
    selem  = as->get3rd( );
  }

  Enode * newDiff = cons( symb, cons( a, cons( b ) ) );

  return newDiff;
}

Enode * Egraph::mkCostIncur( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 3 );
  return cons( id_to_enode[ ENODE_ID_CTINCUR ], args );
}

Enode * Egraph::mkCostBound( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 2 );
  return cons( id_to_enode[ ENODE_ID_CTBOUND ], args );
}

Enode * Egraph::mkEq( Enode * args )
{
  assert( args );
  assert( args->isList( ) );
  assert( args->getCar( ) );
  assert( args->getCdr( )->getCar( ) );

  Enode * x = args->getCar( );
  Enode * y = args->getCdr( )->getCar( );

  // TODO: do type check
  // assert( x->getRetSort( ) == y->getRetSort( ) );

  if ( x->hasSortBool( ) )
    return mkIff( args );

  // Two equal terms
  // x = x => true
  if ( x == y )
    return mkTrue( );

  // Two different constants
  // 1 = 0 => false
  if ( x->isConstant( ) && y->isConstant( ) )
    return mkFalse( );

  if ( x->getId( ) > y->getId( ) )
    args = cons( y, cons( x ) );

  return cons( id_to_enode[ ENODE_ID_EQ ], args );
}

Enode * Egraph::mkLeq( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 2 );

  Enode * x = args->getCar( );
  Enode * y = args->getCdr( )->getCar( );

  assert( !x->hasSortBool( ) );
  assert( !y->hasSortBool( ) );

  // Two equal terms
  // x = x => true
  if ( x == y )
    return mkTrue( );

  // Two constants: evaluate
  if ( x->isConstant( ) && y->isConstant( ) )
    return x->getValue( ) <= y->getValue( )
         ? mkTrue ( )
	 : mkFalse( );

  Enode * res = cons( id_to_enode[ ENODE_ID_LEQ ], args );
  return res;
}

Enode * Egraph::mkPlus( Enode * args )
{
  assert( args );
  assert( args->getArity( ) >= 1 );

  if ( args->getArity( ) == 1 )
    return args->getCar( );

  Enode * res = NULL;
  Enode * x = args->getCar( );
  Enode * y = args->getCdr( )->getCar( );
  //
  // Simplify constants
  //
  if ( x->isConstant( ) && y->isConstant( ) && args->getArity( ) == 2 )
  {
    const Real & xval = x->getValue( );
    const Real & yval = y->getValue( );
    Real sum = xval + yval;
    res = mkNum( sum );
  }
  else
  {
    res = cons( id_to_enode[ ENODE_ID_PLUS ], args );
  }

  assert( res );
  return res;
}

Enode * Egraph::mkMinus( Enode * args )
{
  assert( args );

  if ( args->getArity( ) == 1 )
    return mkUminus( args );

  assert( args->getArity( ) == 2 );

  Enode * res = NULL;

  Enode * x = args->getCar( );
  Enode * y = args->getCdr( )->getCar( );
  Enode * mo = mkNum( "-1" );

  res = mkPlus( cons( x, cons( mkTimes( cons( mo, cons( y ) ) ) ) ) );

  return res;
}

Enode * Egraph::mkUminus( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 1 );

  Enode * x = args->getCar( );
  Enode * mo = mkNum( "-1" );

  return mkTimes( cons( mo, cons( x ) ) );
}

Enode * Egraph::mkTimes( Enode * args )
{
  assert( args );
  assert( args->getArity( ) >= 2 );

  Enode * res = NULL;
  Enode * x = args->getCar( );
  Enode * y = args->getCdr( )->getCar( );

  Real zero_ = 0;
  Enode * zero = mkNum( zero_ );
  //
  // x * 0 --> 0
  //
  if ( x == zero || y == zero )
  {
    res = zero;
  }
  //
  // Simplify constants
  //
  else if ( x->isConstant( ) && y->isConstant( ) )
  {
    const Real & xval = x->getValue( );
    const Real & yval = y->getValue( );
    Real times = xval * yval;
    res = mkNum( times );
  }
  else
  {
    res = cons( id_to_enode[ ENODE_ID_TIMES ], args );
  }
  assert( res );
  return res;
}

Enode * Egraph::mkDiv( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 2 );

  Enode * res = NULL;
  Enode * x = args->getCar( );
  Enode * y = args->getCdr( )->getCar( );

  Real zero_ = 0;
  Enode * zero = mkNum( zero_ );

  if ( y == zero )
    opensmt_error2( "explicit division by zero in formula", "" );

  //
  // 0 * x --> 0
  //
  if ( x == zero )
  {
    res = zero;
  }
  //
  // Simplify constants
  //
  else if ( x->isConstant( ) && y->isConstant( ) )
  {
    const Real & xval = x->getValue( );
    const Real & yval = y->getValue( );
    Real div = xval / yval;
    res = mkNum( div );
  }
  else
  {
    res = cons( id_to_enode[ ENODE_ID_DIV ], args );
  }

  assert( res );
  return res;
}

Enode * Egraph::mkNot( Enode * args )
{
  assert( args );
  assert( args->isList( ) );
  assert( args->getCar( ) );
  Enode * arg = args->getCar( );
  assert( arg->hasSortBool( ) );
  assert( arg->isTerm( ) );

  // not not p --> p
  if ( arg->isNot( ) )
    return arg->get1st( );

  // not false --> true
  if ( arg->isFalse( ) )
    return mkTrue( );

  // not true --> false
  if ( arg->isTrue( ) )
    return mkFalse( );

  return cons( id_to_enode[ ENODE_ID_NOT ], args );
}

Enode * Egraph::mkAnd( Enode * args )
{
  assert( args );
  assert( args->isList( ) );

  // Prepare + fast path
  unsigned count = 0;
  Enode *res = NULL;
  for ( Enode * alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
  {
    Enode * e = alist->getCar( );
    assert( e->hasSortBool( ) );

    if ( e->isFalse( ) )
      return mkFalse();
    if ( e->isTrue( ) ) continue;
    res = e;
    count++;
  }
  if ( count == 0 )
    return mkTrue( );
  if ( count == 1 )
    return res;

  Enode* new_args[count];
  count = 0;

  // Filter duplicates
  initDup1( );
  for ( Enode * alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
  {
    Enode * e = alist->getCar( );

    if ( e->isTrue( ) ) continue;
    if ( isDup1( e ) ) continue;

    new_args[count] = e;
    storeDup1( e );
    count++;
  }

  assert (count != 0);

  // Make the cons
  doneDup1( );

  res = NULL;

  if ( count == 1 )
    return new_args[0];
  else
    return cons( id_to_enode[ ENODE_ID_AND ], cons( new_args, count ) );
}

Enode * Egraph::mkOr( Enode * args )
{
  assert( args );
  assert( args->isList( ) );

  // Prepare + fast path
  unsigned count = 0;
  Enode* res = NULL;
  for ( Enode * alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
  {
    Enode * e = alist->getCar( );
    assert( e->hasSortBool( ) );

    if ( e->isTrue( ) )
      return mkTrue();
    if ( e->isFalse( ) ) continue;
    res = e;
    count++;
  }
  if ( count == 0 )
    return mkFalse( );
  if ( count == 1 )
    return res;

  Enode* new_args[count];
  count = 0;

  // Filter duplicates
  initDup1( );
  for ( Enode * alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
  {
    Enode * e = alist->getCar( );

    if ( e->isFalse( ) ) continue;
    if ( isDup1( e ) ) continue;

    new_args[count] = e;
    storeDup1( e );
    count++;
  }

  assert (count != 0);

  // Make the cons
  doneDup1( );

  res = NULL;

  if ( count == 1 )
    return new_args[0];
  else
    return cons( id_to_enode[ ENODE_ID_OR ], cons( new_args, count ) );
}

Enode * Egraph::mkIff( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 2 );
  Enode * first  = args->getCar( );
  Enode * second = args->getCdr( )->getCar( );

  if ( first ->isTrue ( ) )               return second;
  if ( first ->isFalse( ) )               return mkNot( cons( second ) );
  if ( second->isTrue ( ) )               return first;
  if ( second->isFalse( ) )               return mkNot( cons( first ) );
  if ( first == second )                  return mkTrue ( );
  if ( first == mkNot( cons( second ) ) ) return mkFalse( );

  return cons( id_to_enode[ ENODE_ID_EQ ], args );
}

Enode * Egraph::mkIte( Enode * args )
{
  assert( args );
  Enode * i = args->getCar( );
  Enode * t = args->getCdr( )->getCar( );
  Enode * e = args->getCdr( )->getCdr( )->getCar( );
  return mkIte( i, t, e );
}

Enode * Egraph::mkIte( Enode * i, Enode * t, Enode * e )
{
  assert( i );
  assert( t );
  assert( e );
  Snode * ts = t->getRetSort( );
  Snode * es = e->getRetSort( );
  Snode * is = i->getRetSort( );
  assert( !ts->getCar( )->isPara( ) );
  assert( !es->getCar( )->isPara( ) );
  assert( ts == es );
  assert( i->hasSortBool( ) );

  if ( i->isTrue( )  ) return t;
  if ( i->isFalse( ) ) return e;
  if ( t == e )        return t;

  has_ites = true;
  //
  // ITE has a parametric sort. We make sure that
  // an ITE with current sorts exists, in case we
  // create it
  //
  stringstream ss;
  ss << "ite " << is << " " << ts << " " << es;
  Enode * symb = lookupSymbol( ss.str( ).c_str( ) );
  if ( symb == NULL )
  {
    Snode * site = sort_store.mkDot( sort_store.cons( is
	                           , sort_store.cons( ts
			  	   , sort_store.cons( es ) ) ) );
    symb = newSymbol( "ite", site, ts ); 
  }

  return cons( symb
             , cons( i
             , cons( t
	     , cons( e ) ) ) );
}

Enode * Egraph::mkXor( Enode * args )
{
  assert( args );

  assert( args->getArity( ) == 2 );
  Enode * first  = args->getCar( );
  Enode * second = args->getCdr( )->getCar( );
  assert( first->hasSortBool( ) );
  assert( second->hasSortBool( ) );

  if ( first ->isFalse( ) )               return second;
  if ( first ->isTrue ( ) )               return mkNot( cons( second ) );
  if ( second->isFalse( ) )               return first;
  if ( second->isTrue ( ) )               return mkNot( cons( first ) );
  if ( first == second )                  return mkFalse( );
  if ( first == mkNot( cons( second ) ) ) return mkTrue ( );

  return cons( id_to_enode[ ENODE_ID_XOR ], args );
}

Enode * Egraph::mkImplies( Enode * args )
{
  assert( args );

  Enode * first  = args->getCar( );
  Enode * second = args->getCdr( )->getCar( );
  Enode * not_first = mkNot( cons( first ) );

  if ( first ->isFalse( ) ) return mkTrue( );
  if ( second->isTrue ( ) ) return mkTrue( );
  if ( first ->isTrue ( ) ) return second;
  if ( second->isFalse( ) ) return not_first;

  return mkOr( cons( not_first
	     , cons( second ) ) );
}

Enode * Egraph::mkDistinct( Enode * args )
{
  assert( args );
  Enode * res = NULL;
  //
  // Replace distinction with negated equality when it has only 2 args
  //
  if ( args->getArity( ) == 2 )
  {
    Enode * x = args->getCar( );
    Enode * y = args->getCdr( )->getCar( );
    res = mkNot( cons( mkEq( cons( x, cons( y ) ) ) ) );
  }
  else
  {
    res = cons( id_to_enode[ ENODE_ID_DISTINCT ], args );

    // The thing is that this distinction might have been
    // already processed. So if the index is -1 we are sure
    // it is new
    if ( !config.incremental
      && res->getDistIndex( ) == -1 )
    {
      size_t index = index_to_dist.size( );

      if ( index > sizeof( dist_t ) * 8 )
	opensmt_error2( "max number of distinctions supported is " ,sizeof( dist_t ) * 8 );

      res->setDistIndex( index );
      // Store the correspondence
      index_to_dist.push_back( res );
      // Check invariant
      assert( index_to_dist[ index ] == res );
    }
  }

  assert( res );
  return res;
}

//=================================================================================================
// Bit-Vector routines FIXME: to be fixed w.r.t. SMTLIB2

/*
Enode * Egraph::mkRepeat( int n, Enode * x )
{
  assert( x );
  Enode * res = x;
  for ( int i = 1 ; i < n ; i ++ )
    res = mkConcat( cons( x, cons( res ) ) );
  assert( res->getWidth( ) == n * x->getWidth( ) );
  return res;
}
*/

/*
Enode * Egraph::mkBvnum( char * str )
{
  Enode * new_enode = NULL;

  if ( str[ 0 ] == 'b'
    && str[ 1 ] == 'v'
    && str[ 2 ] != 'b' )
  {
    char * end_value = strchr( str, '[' );
    char * p = &(str[2]);

    int width = 0;
    sscanf( end_value, "[%d]", &width );
    assert( width > 0 );
    //
    // Copy relevant part of the string
    //
    char dec_value_str[ width ];
    char * q = dec_value_str;
    while ( p != end_value ) *q ++ = *p ++;
    *q = '\0';
    //
    // Allocate a mp number
    //
    mpz_class dec_value( dec_value_str );
    //
    // Compute value with leading zeros
    //

    string value;
    value.insert( 0, width - dec_value.get_str( 2 ).size( ), '0' );
    value = value + dec_value.get_str( 2 );

    assert( (int)strlen( value.c_str( ) ) == width );

    new_enode = new Enode( id_to_enode.size( )
			 , value.c_str( )
			 , ETYPE_NUMB
			 , DTYPE_BITVEC | width );
  }
  else if ( str[ 0 ] == 'b'
         && str[ 1 ] == 'v'
         && str[ 2 ] == 'b'
         && str[ 3 ] == 'i'
	 && str[ 4 ] == 'n' )
  {
    int width = strlen( str ) - 5;

    new_enode = new Enode( id_to_enode.size( )
			 , &(str[ 5 ])
	                 , ETYPE_NUMB
			 , DTYPE_BITVEC | width );
  }
  else
  {
    int width = strlen( str );
			 , ETYPE_NUMB
			 , DTYPE_BITVEC | width );
  }
  assert( new_enode );
  Enode * res = insertNumber( new_enode );

  return cons( res );
}
*/

/*
Enode * Egraph::mkExtract( int msb, int lsb, Enode * arg )
{
  assert( arg );
  assert( msb >= 0 );
  assert( 0 <= lsb );
  assert( lsb <= msb );
  assert( msb <= arg->getWidth( ) - 1 );

  Enode * res = NULL;

  const int i = msb, j = lsb;
  int arg_msb, arg_lsb;
  //
  // Apply rewrite rules. We assume x to have width n, y to have width m
  //
  // Rule 1:
  // x[n-1:0] --> x
  //
  if ( arg->getWidth( ) == i - j + 1 )
    res = arg;
  //
  // Rewrite rule for extraction
  //
  // x[msb:lsb][i:j] --> x[i+lsb:j+lsb]
  //
  else if ( arg->isExtract( &arg_msb, &arg_lsb ) )
  {
    Enode * arg_arg = arg->getCdr( )->getCar( );
    assert( !arg_arg->isExtract( ) );
    res = mkExtract( i + arg_lsb, j + arg_lsb, arg_arg );
  }
  //
  // Rewrite rules for concatenation
  //
  else if ( arg->isConcat( )
         || arg->isCbe   ( ) )
  {
    list< Enode * > new_args;
    int width_left = arg->getWidth( );

    for ( Enode * list = arg->getCdr( )
	; !list->isEnil( )
	; list = list->getCdr( ) )
    {
      Enode * conc = list->getCar( );
      const int conc_width = conc->getWidth( );
      const int rem_width = width_left - conc_width;
      width_left = rem_width;
      // Compute current extraction indexes
      int real_msb = i - rem_width;
      int real_lsb = j - rem_width;
      // Continue if this slice is out of msb:lsb
      if ( real_msb < 0 || real_lsb >= conc_width )
	continue;
      // Fix indexes if out of bounds
      if ( real_msb >= conc_width ) real_msb = conc_width - 1;
      if ( real_lsb <  0 )          real_lsb = 0;
      // Add slice to list
      new_args.push_front( mkExtract( real_msb, real_lsb, conc ) );
    }
    if ( arg->isConcat( ) )
      res = mkConcat( cons( new_args ) );
    else
      res = mkCbe   ( cons( new_args ) );
  }
  //
  // Rewrite a selected number as the equivalent number
  //
  else if ( arg->isConstant( ) )
  {
    const char * value = arg->getCar( )->getName( );
    int width = arg->getWidth( );

    char new_value[ i - j + 2 ];
    const int bit_i = width - 1 - i;
    const int bit_j = width - 1 - j;

    for ( int h = bit_i ; h <= bit_j ; h ++ )
      new_value[ h - bit_i ] = value[ h ];

    new_value[ i - j + 1 ] = '\0';

    assert( (int)strlen( new_value ) == i - j + 1 );

    res = mkBvnum( new_value );
  }
  else
  {
    const Pair( int ) sig = make_pair( msb, lsb );
    MapPairEnode::iterator it = ext_store.find( sig );
    Enode * e = NULL;
    if ( it == ext_store.end( ) )
    {
      char name[ 256 ];
      sprintf( name, "extract[%d:%d]", msb, lsb );
      assert( lookupSymbol( name ) == NULL );
      e = newSymbol( name, DTYPE_BITVEC | (msb - lsb + 1) );
      e->setExtract( lsb );
      ext_store[ sig ] = e;
    }
    else
    {
      e = it->second;
    }
    assert( e );
    res = cons( e, cons( arg ) );
  }

  assert( res );
  return res;
}

Enode * Egraph::mkConcat( Enode * args )
{
  assert( args );

  Enode * res = NULL;

  if ( args->getArity( ) == 1 )
  {
     res = args->getCar( );
  }
  else
  {
    assert( args->getArity( ) >= 2 );

    Enode * a = args->getCar( );
    Enode * b = args->getCdr( )->getCar( );

    if ( args->getArity( ) == 2
      && a->isConstant ( )
      && b->isConstant ( ) )
    {
      char str[ strlen( a->getCar( )->getName( ) ) + strlen( b->getCar( )->getName( ) ) + 1 ];
      strcpy( str, a->getCar( )->getName( ) );
      strcat( str, b->getCar( )->getName( ) );
      res = mkBvnum( str );
    }
    else
    {
      list< Enode * > new_args;
      for ( Enode * list = args ; !list->isEnil( ) ; list = list->getCdr( ) )
      {
	Enode * e = list->getCar( );
	assert( e->isDTypeBitVec( ) );

	// Add arguments instead
	if ( e->isConcat( ) )
	  for ( Enode * l = e->getCdr( ) ; !l->isEnil( ) ; l = l->getCdr( ) )
	    new_args.push_front( l->getCar( ) );
	else
	  new_args.push_front( e );
      }

      res = cons( id_to_enode[ ENODE_ID_CONCAT ], cons( new_args ) );
    }
  }

  assert( res );
  return res;
}

Enode * Egraph::mkCbe( Enode * args )
{
  assert( args );
  assert( args->getArity( ) >= 1 );

  if ( args->getArity( ) == 1 )
    return args->getCar( );

  return cons( id_to_enode[ ENODE_ID_CBE ], args );
}

Enode * Egraph::mkBvadd ( Enode * args )
{
  assert( args );

  if ( args->getArity( ) == 1 )
    return args->getCar( );

  assert( args->getArity( ) == 2 );
  Enode * a = args->getCar( );
  Enode * b = args->getCdr( )->getCar( );

  assert( a->isDTypeBitVec( ) );
  assert( b->isDTypeBitVec( ) );
  assert( a->getWidth( ) == b->getWidth( ) );

  const int width = a->getWidth( );
  string zero_str;
  zero_str.insert( 0, width, '0' );
  Enode * zero = mkBvnum( const_cast< char * >( zero_str.c_str( ) ) );
  //
  // a + 0 = a, b + 0 = b
  //
  if ( a == zero ) return b;
  if ( b == zero ) return a;

  Enode * res = NULL;
  //
  // Both numbers are constants, simplify
  //
  if ( a->isConstant( ) && b->isConstant( ) )
  {
    mpz_class aval( a->getCar( )->getName( ), 2 );
    mpz_class bval( b->getCar( )->getName( ), 2 );
    aval = aval + bval;
    Enode * res = makeNumberFromGmp( aval, width );
    return res;
  }
  else
    res = cons( id_to_enode[ ENODE_ID_BVADD ], args );

  assert( res );
  return res;
}

Enode * Egraph::mkBvmul ( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 2 );
  Enode * a = args->getCar( );
  Enode * b = args->getCdr( )->getCar( );

  assert( a->getWidth( ) == b->getWidth( ) );

  const int width = a->getWidth( );

  if ( a->isConstant( ) && b->isConstant( ) )
  {
    mpz_class aval( a->getCar( )->getName( ), 2 );
    mpz_class bval( b->getCar( )->getName( ), 2 );
    aval = aval * bval;
    return makeNumberFromGmp( aval, width );
  }

  if ( a->isConstant( ) && !b->isConstant( ) )
  {
    Enode * tmp = a;
    a = b;
    b = tmp;
  }

  string zero_str;
  zero_str.insert( 0, width, '0' );
  Enode * zero = mkBvnum( const_cast< char * >( zero_str.c_str( ) ) );
  string one_str;
  one_str.insert( 0, width - 1, '0' );
  one_str.push_back( '1' );
  Enode * one = mkBvnum( const_cast< char * >( one_str.c_str( ) ) );

  Enode * res = NULL;
  if ( a == zero || b == zero ) res = zero;
  else if ( a == one ) res = b;
  else if ( b == one ) res = a;
  else res = cons( id_to_enode[ ENODE_ID_BVMUL ], args );

  assert( res );
  return res;
}

//
// Translate signed division into unsigned one
//
Enode * Egraph::mkBvsdiv ( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 2 );
  Enode * s = args->getCar( );
  Enode * t = args->getCdr( )->getCar( );
  assert( s->getWidth( ) == t->getWidth( ) );
  const int width = s->getWidth( );

  Enode * msb_s = mkExtract( width - 1, width - 1, s );
  Enode * msb_t = mkExtract( width - 1, width - 1, t );
  Enode * bit0  = mkBvnum( const_cast< char * >( "0" ) );
  Enode * bit1  = mkBvnum( const_cast< char * >( "1" ) );

  Enode * cond1 = mkAnd( cons( mkEq( cons( msb_s, cons( bit0 ) ) )
                       , cons( mkEq( cons( msb_t, cons( bit0 ) ) )
		       ) ) );

  Enode * case1 = mkBvudiv( cons( s, cons( t ) ) );

  Enode * cond2 = mkAnd( cons( mkEq( cons( msb_s, cons( bit1 ) ) )
                       , cons( mkEq( cons( msb_t, cons( bit0 ) ) )
		       ) ) );

  Enode * case2 = mkBvneg( cons( mkBvudiv( cons( mkBvneg( cons( s ) ), cons( t ) ) ) ) );

  Enode * cond3 = mkAnd( cons( mkEq( cons( msb_s, cons( bit0 ) ) )
                       , cons( mkEq( cons( msb_t, cons( bit1 ) ) )
		       ) ) );

  Enode * case3 = mkBvneg( cons( mkBvudiv( cons( s, cons( mkBvneg( cons( t ) ) ) ) ) ) );

  Enode * case4 = mkBvudiv( cons( mkBvneg( cons( s ) ), cons( mkBvneg( cons( t ) ) ) ) );

  Enode * res = mkIte( cond1
                     , case1
	             , mkIte( cond2
			    , case2
			    , mkIte( cond3
			           , case3
			           , case4 ) ) );

  return res;
}

//
// Translate signed division into unsigned one
//
Enode * Egraph::mkBvsrem ( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 2 );
  Enode * s = args->getCar( );
  Enode * t = args->getCdr( )->getCar( );
  assert( s->getWidth( ) == t->getWidth( ) );
  const int width = s->getWidth( );

  Enode * msb_s = mkExtract( width - 1, width - 1, s );
  Enode * msb_t = mkExtract( width - 1, width - 1, t );
  Enode * bit0  = mkBvnum( const_cast< char * >( "0" ) );
  Enode * bit1  = mkBvnum( const_cast< char * >( "1" ) );

  Enode * cond1 = mkAnd( cons( mkEq( cons( msb_s, cons( bit0 ) ) )
                       , cons( mkEq( cons( msb_t, cons( bit0 ) ) )
		       ) ) );

  Enode * case1 = mkBvurem( cons( s, cons( t ) ) );

  Enode * cond2 = mkAnd( cons( mkEq( cons( msb_s, cons( bit1 ) ) )
                       , cons( mkEq( cons( msb_t, cons( bit0 ) ) )
		       ) ) );

  Enode * case2 = mkBvneg( cons( mkBvurem( cons( mkBvneg( cons( s ) ), cons( t ) ) ) ) );

  Enode * cond3 = mkAnd( cons( mkEq( cons( msb_s, cons( bit0 ) ) )
                       , cons( mkEq( cons( msb_t, cons( bit1 ) ) )
		       ) ) );

  Enode * case3 = mkBvurem( cons( s, cons( mkBvneg( cons( t ) ) ) ) );

  Enode * case4 = mkBvneg( cons( mkBvurem( cons( mkBvneg( cons( s ) ), cons( mkBvneg( cons( t ) ) ) ) ) ) );

  Enode * res = mkIte( cond1
                     , case1
	             , mkIte( cond2
			    , case2
			    , mkIte( cond3
			           , case3
			           , case4 ) ) );

  return res;
}
//
// Logical shift right
//
Enode * Egraph::mkBvlshr ( Enode * args )
{
  assert( args );
  Enode * t1 = args->getCar( );
  Enode * t2  = args->getCdr( )->getCar( );

  if ( t2->isConstant( ) )
  {
    Enode * num = t2;
    Enode * term = t1;
    //
    // Convert number into decimal
    //
    const int num_width = num->getWidth( );
    const char * str = num->getCar( )->getName( );

    assert( num_width == (int)strlen( str ) );
    //
    // Skip leading zeros
    //
    int i;
    for ( i = 0 ; i < num_width && str[ i ] == '0' ; i ++ )
      ;
    //
    // Return term if shift by zero
    //
    if ( i == num_width )
      return term;

    i ++;
    unsigned dec_value = 1;
    for ( ; i < num_width ; i ++ )
    {
      dec_value = dec_value << 1;
      if ( str[ i ] == '1' )
	dec_value ++;
    }

    const int term_width = term->getWidth( );

    if( (int)dec_value >= term->getWidth( ) )
    {
      string zero;
      zero.insert( 0, term->getWidth( ), '0' );
      Enode * res = mkBvnum ( const_cast< char * >( zero.c_str( ) ) );
      assert( res->getWidth( ) == term->getWidth( ) );
      return res;
    }

    assert( (int)dec_value < term->getWidth( ) );
    //
    // Translate shift into concatenation and extraction
    //
    Enode * ext = mkExtract( term_width - 1, dec_value, term );
    assert( ext->getWidth( ) == term_width - (int)dec_value );

    string leading_zeros;
    leading_zeros.insert( 0, dec_value, '0' );

    Enode * lea = mkBvnum ( const_cast< char * >( leading_zeros.c_str( ) ) );
    Enode * con = mkConcat( cons( lea, cons( ext ) ) );

    assert( con->getWidth( ) == term->getWidth( ) );
    return con;
  }
  //
  // Aumount of shifting is unknown
  //
  else
  {
    Enode * res = t1;
    Enode * one = mkBvnum( const_cast< char * >( "1" ) );
    for ( int i = 0 ; i < t2->getWidth( ) ; i ++ )
    {
      Enode * ite_i = mkEq( cons( mkExtract( i, i, t2 ), cons( one ) ) );
      string l_zeros;
      string t_zeros;
      l_zeros.insert( 0, t2->getWidth( ) - i - 1, '0' );
      t_zeros.insert( 0, i, '0' );
      string num_str_1 = l_zeros + "1" + t_zeros;
      Enode * ite_t = mkBvlshr( cons( res, cons( mkBvnum( const_cast< char * >( num_str_1.c_str( ) ) ) ) ) ); 
      res = mkIte( ite_i, ite_t, res );
    }

    return res;
  }

  assert( false );
  return NULL;
}

//
// Arithmetic shift right
//
Enode * Egraph::mkBvashr ( Enode * args )
{
  assert( args );
  Enode * t1 = args->getCar( );
  Enode * t2 = args->getCdr( )->getCar( );
  Enode * ext  = mkExtract( t1->getWidth( ) - 1, t1->getWidth( ) - 1, t1 );
  Enode * zero = mkBvnum( const_cast< char * >( "0" ) );
  Enode * i = mkEq( cons( ext, cons( zero ) ) );
  Enode * t = mkBvlshr( cons( t1, cons( t2 ) ) );
  Enode * e = mkBvnot( cons( mkBvlshr( cons( mkBvnot( cons( t1 ) ), cons( t2 ) ) ) ) );
  return mkIte( i, t, e );
}

//
// Rotate left
// Rewrite as x[width-i-1:0]::x[width-1:width-i]
//              x[j_h:i_h]::x[j_l:i_l]
//
Enode * Egraph::mkRotateLeft( int i, Enode * x )
{
  assert( x );
  assert( x->isTerm( ) );
  const int width = x->getWidth( );

  i = i % width;
  if ( i == 0 )
    return x;

  const int j_h = width - i - 1;
  const int i_h = 0;
  const int j_l = width - 1;
  const int i_l = width - i;
  assert( j_h - i_h + 1 + j_l - i_l + 1 == width );
  Enode * h = mkExtract( j_h, i_h, x );
  Enode * l = mkExtract( j_l, i_l, x );
  return mkConcat( cons( h, cons( l ) ) );
}

//
// Rotate right
// Rewrite as x[i-1:0]::x[width-1:i]
//          x[j_h:i_h]::x[j_l:i_l]
//
Enode * Egraph::mkRotateRight( int i, Enode * x )
{
  assert( x );
  assert( x->isTerm( ) );
  const int width = x->getWidth( );

  i = i % width;
  if ( i == 0 )
    return x;

  const int j_h = i - 1;
  const int i_h = 0;
  const int j_l = width - 1;
  const int i_l = i;
  assert( j_h - i_h + 1 + j_l - i_l + 1 == width );
  Enode * h = mkExtract( j_h, i_h, x );
  Enode * l = mkExtract( j_l, i_l, x );
  return mkConcat( cons( h, cons( l ) ) );
}

//
// Shift left
//
Enode * Egraph::mkBvshl ( Enode * args )
{
  assert( args );
  Enode * term = args->getCar( );
  Enode * num  = args->getCdr( )->getCar( );

  if ( term->isConstant( )
    && !num->isConstant( ) )
  {
    //
    // Special case for spear benchmarks
    //
    string one;
    one.insert( 0, term->getWidth( ) - 1, '0' );
    one += '1';
    string zero;
    zero.insert( 0, term->getWidth( ), '0' );
    Enode * bv_one  = mkBvnum( const_cast< char * >( one .c_str( ) ) );
    Enode * bv_zero = mkBvnum( const_cast< char * >( zero.c_str( ) ) );
    if ( term == bv_one )
      return mkIte( mkEq( cons( num, cons( bv_zero ) ) ), term, bv_zero );
  }

  if ( num->isConstant( ) )
  {
    //
    // Convert number into decimal
    //
    const int num_width = num->getWidth( );
    const char * str = num->getCar( )->getName( );

    assert( num_width == (int)strlen( str ) );
    //
    // Skip leading zeros
    //
    int i;
    for ( i = 0 ; i < num_width && str[ i ] == '0' ; i ++ )
      ; // Do nothing
    //
    // Return term if shift by zero
    //
    assert( i <= num_width );
    assert( i != num_width || str[ i - 1 ] == '0' );
    if ( i == num_width )
      return term;

    i ++;
    mpz_class dec_value_gmp = 1;
    for ( ; i < num_width ; i ++ )
    {
      dec_value_gmp = dec_value_gmp << 1;
      if ( str[ i ] == '1' )
	dec_value_gmp ++;
    }

    mpz_class term_width_gmp = mpz_class( term->getWidth( ) );
    if( dec_value_gmp >= term_width_gmp )
    {
      string zero;
      zero.insert( 0, term->getWidth( ), '0' );
      Enode * res = mkBvnum ( const_cast< char * >( zero.c_str( ) ) );
      assert( res->getWidth( ) == term->getWidth( ) );
      return res;
    }

    assert( dec_value_gmp.fits_sint_p( ) );
    const int dec_value = dec_value_gmp.get_si( );
    const int term_width = term->getWidth( );

    assert( dec_value < term->getWidth( ) );
    //
    // Translate shift into concatenation and extraction
    //
    Enode * ext = mkExtract( term_width - dec_value - 1, 0, term );

    string trailing_zeros;
    trailing_zeros.insert( 0, dec_value, '0' );

    Enode * tra = mkBvnum ( const_cast< char * >( trailing_zeros.c_str( ) ) );
    Enode * con = mkConcat( cons( ext, cons( tra ) ) );

    assert( con->getWidth( ) == term->getWidth( ) );

    return con;
  }
  //
  // Aumount of shifting is unknown
  //
  else
  {
    Enode * res = term;
    Enode * t2 = num;
    Enode * one = mkBvnum( const_cast< char * >( "1" ) );
    for ( int i = 0 ; i < t2->getWidth( ) ; i ++ )
    {
      Enode * ite_i = mkEq( cons( mkExtract( i, i, t2 ), cons( one ) ) );
      string l_zeros;
      string t_zeros;
      l_zeros.insert( 0, t2->getWidth( ) - i - 1, '0' );
      t_zeros.insert( 0, i, '0' );
      string num_str_1 = l_zeros + "1" + t_zeros;
      Enode * ite_t = mkBvshl( cons( res, cons( mkBvnum( const_cast< char * >( num_str_1.c_str( ) ) ) ) ) ); 
      res = mkIte( ite_i, ite_t, res );
    }

    return res;
  }
}

//
// Translate it into (bvadd (bvnot x) 1)
//
Enode * Egraph::mkBvneg( Enode * args )
{
  assert( args->getArity( ) == 1 );
  Enode * bvnot = mkBvnot( args );
  Enode * e = args->getCar( );
  string num_str;
  num_str.insert( 0, e->getWidth( ) - 1, '0' );
  num_str.push_back( '1' );
  Enode * bvnum = mkBvnum( const_cast< char * >( num_str.c_str( ) ) );
  return mkBvadd( cons( bvnot, cons( bvnum ) ) );
}

Enode * Egraph::mkBvsub( Enode * args )
{
  Enode * a = args->getCar( );
  Enode * b = args->getCdr( )->getCar( );
  char buf[ 32 ];
  sprintf( buf, "bv1[%d]", a->getWidth( ) );
  Enode * neg_b = mkBvneg( cons( b ) );
  Enode * res   = mkBvadd( cons( a, cons( neg_b ) ) );
  return res;
}

Enode * Egraph::mkBvand( Enode * args )
{
  assert( args );
  assert( args->isList( ) );
  Enode * res = NULL;

  Enode * bv0 = mkBvnum( const_cast< char * >( "0" ) );
  Enode * bv1 = mkBvnum( const_cast< char * >( "1" ) );

  initDup1( );

  list< Enode * > new_args;
  for ( Enode * list = args ; !list->isEnil( ) ; list = list->getCdr( ) )
  {
    Enode * e = list->getCar( );
    assert( e->isDTypeBitVec( ) );

    if ( isDup1( e ) ) continue;

    if ( e == bv1 )
      continue;

    if ( e == bv0 )
    {
      doneDup1( );
      return bv0;
    }

    new_args.push_front( e );
    storeDup1( e );

    assert( (*new_args.begin( ))->getWidth( ) == new_args.back( )->getWidth( ) );
  }

  doneDup1( );

  if ( new_args.size( ) == 0 )
    res = bv1;
  else if ( new_args.size( ) == 1 )
    res = new_args.back( );
  else
    res = cons( id_to_enode[ ENODE_ID_BVAND ], cons( new_args ) );

  assert( res );
  return res;
}

Enode * Egraph::mkBvor( Enode * args )
{
  assert( args );

  Enode * res = NULL;
  Enode * bv0 = mkBvnum( const_cast< char * >( "0" ) );
  Enode * bv1 = mkBvnum( const_cast< char * >( "1" ) );

  initDup1( );
  list< Enode * > new_args;
  for ( Enode * list = args ; !list->isEnil( ) ; list = list->getCdr( ) )
  {
    Enode * e = list->getCar( );
    assert( e->isDTypeBitVec( ) );

    // Redundant argument
    if ( e == bv0 )
      continue;
    // Return 1 if 1 is an argument
    if ( e == bv1 ) { doneDup1( ); return bv1; }

    if ( isDup1( e ) )
      continue;

    new_args.push_front( e );
    storeDup1( e );

    assert( (*new_args.begin( ))->getWidth( ) == new_args.back( )->getWidth( ) );
  }
  doneDup1( );

  if ( new_args.size( ) == 0 )
    res = bv0;
  else if ( new_args.size( ) == 1 )
    res = new_args.back( );
  else
    res = cons( id_to_enode[ ENODE_ID_BVOR ], cons( new_args ) );

  assert( res );
  return res;
}

Enode * Egraph::mkBvnot( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 1 );
  Enode * arg = args->getCar( );
  assert( arg->isDTypeBitVec( ) );

  Enode * res = NULL;

  if ( arg->isConstant( ) )
  {
    const char * bin_value = arg->getCar( )->getName( );
    char new_bin_value[ strlen( bin_value ) + 1 ];
    unsigned i;
    for ( i = 0 ; i < strlen( bin_value ) ; i ++ )
      new_bin_value[ i ] = ( bin_value[ i ] == '0' ? '1' : '0' );
    new_bin_value[ i ] = '\0';

    assert( strlen( new_bin_value ) == strlen( bin_value ) );
    res = mkBvnum( new_bin_value );
  }
  //
  // (bvnot (bvnot x)) --> x
  //
  else if ( arg->isBvnot( ) )
    res = arg->get1st( );
  else
    res = cons( id_to_enode[ ENODE_ID_BVNOT ], args );

  assert( res );
  return res;
}

Enode * Egraph::mkBvxor( Enode * args )
{
  assert( args );
  assert( args->getArity( ) == 2 );
  Enode * a = args->getCar( );
  Enode * b = args->getCdr( )->getCar( );
  Enode * res = NULL;

  if( a->isConstant( ) && b->isConstant( ) )
  {
    const char * a_value = a->getCar( )->getName( );
    const char * b_value = b->getCar( )->getName( );
    char new_value[ strlen( a_value ) + 1 ];

    assert( strlen( b_value ) == strlen( a_value ) );

    unsigned i;
    for ( i = 0 ; i < strlen( a_value ) ; i ++ )
      new_value[ i ] = ( a_value[ i ] == b_value[ i ] ? '0' : '1' );
    new_value[ i ] = '\0';

    assert( strlen( new_value ) == strlen( a_value ) );
    res = mkBvnum( new_value );
  }
  else
    res = cons( id_to_enode[ ENODE_ID_BVXOR ], args );

  return res;
}

//
// Sign extend a variable x_n
//
Enode * Egraph::mkSignExtend( int i, Enode * x )
{
  assert( x );
  assert( x->isTerm( ) );

  Enode * res = NULL;

  if ( x->isConstant( ) )
  {
    // Retrieve msb
    const char msb_chr = *(x->getCar( )->getName( ));
    // Generate trailing ones or zeros
    string leading;
    leading.insert( 0, i, msb_chr );
    Enode * extension = mkBvnum( const_cast< char * >( leading.c_str( ) ) );
    res = mkConcat( cons( extension, cons( x ) ) );
  }
  else
  {
    // If already there
    Enode * e = NULL;
    if ( i < static_cast< int >( se_store.size( ) ) 
      && se_store[ i ] != NULL )
      e = se_store[ i ];
    else
    {
      if ( i >= static_cast< int >( se_store.size( ) ) )
	se_store.resize( i + 1, NULL );
      assert( i < static_cast< int >( se_store.size( ) ) );
      assert( se_store[ i ] == NULL );
      char name[ 32 ];
      sprintf( name, "sign_extend[%d]", i );
      assert( lookupSymbol( name ) == NULL );
      e = newSymbol( name, DTYPE_BITVEC | (i + x->getWidth( )) );
      se_store[ i ] = e;
    }

    assert( e );
    res = cons( e, cons( x ) );
    res->setWidth( i + x->getWidth( ) );
  }

  assert( res );
  assert( res->getWidth( ) == i + x->getWidth( ) );
  return res;
}

//
// Zero extend a variable x_n
// Rewritten as (0..0 :: x)
//
Enode * Egraph::mkZeroExtend( int i, Enode * x )
{
  assert( x );
  assert( x->isTerm( ) );
  // Create padding 0s
  string num_str;
  num_str.insert( 0, i, '0' );
  Enode * extend_zero = mkBvnum( const_cast< char * >( num_str.c_str( ) ) );
  // Create extension 0
  Enode * res = mkConcat( cons( extend_zero, cons( x ) ) );
  return res;
}
*/

//=================================================================================================
// Other APIs

//
// Packs assertions and formula and return it into a single enode
//
Enode * Egraph::getUncheckedAssertions( )
{
  if ( assertions.empty( ) )
    return mkTrue( );

  // Pack the formula and the assertions
  // into an AND statement, and return it
  if ( top != NULL )
    assertions.push_back( top );

  Enode * args = cons( assertions );

  // Clear assertions for incremental solving
  assertions.clear( );

  return mkAnd( args );
}

#ifdef PRODUCE_PROOF
Enode * Egraph::getNextAssertion( )
{
  if ( assertions.empty( ) )
    return NULL;

  Enode * ret = assertions.front( );
  assertions.pop_front( );
  return ret;
}

void Egraph::addDefinition( Enode * def, Enode * term )
{
  assert( config.produce_inter != 0 );
  idef_list.push_back( def );
  assert( idef_map.find( def ) == idef_map.end( ) );
  idef_map[ def ] = term;
}

Enode * Egraph::expandDefinitions( Enode * interpolant )
{
  assert( interpolant );
  set< Enode * > idefs_to_undo;
  // Collect all definitions 
  scanForDefs( interpolant, idefs_to_undo );
  Enode * result = interpolant;
  // Undo definitions
  for ( int i = idef_list.size( ) - 1 ; i >= 0 ; i -- )
  {
    Enode * def = idef_list[ i ];
    // Skip definitions not there
    if ( idefs_to_undo.find( def ) == idefs_to_undo.end( ) )
      continue;

    // Replace
    map< Enode *, Enode * > tmp_map;
    tmp_map[ def ] = idef_map[ def ];
    result = substitute( result, tmp_map );
    // Update defs to undo
    scanForDefs( result, idefs_to_undo );
  }

  return result;
}

void Egraph::scanForDefs( Enode * formula
                        , set< Enode * > & idefs_to_undo )
{
  assert( formula );
  vector< Enode * > unprocessed_enodes;
  initDup1( );

  unprocessed_enodes.push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( isDup1( enode ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; arg_list != enil
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );

      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !isDup1( arg ) )
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

    map< Enode *, Enode * >::iterator it = idef_map.find( enode );

    if ( it != idef_map.end( ) )
      idefs_to_undo.insert( enode );

    storeDup1( enode );
  }

  doneDup1( );
}

Enode *
Egraph::substitute( Enode * formula, map< Enode *, Enode * > & substs )
{
  assert( formula );
  vector< Enode * > unprocessed_enodes;
  initDupMap1( );

  unprocessed_enodes.push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; arg_list != enil
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );

      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( valDupMap1( arg ) == NULL )
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

    map< Enode *, Enode * >::iterator it = substs.find( enode );

    Enode * result = NULL;
    if ( it != substs.end( ) )
    {
      assert( enode->isVar( ) );
      result = it->second;
    }
    else
      result = copyEnodeEtypeTermWithCache( enode );

    assert( result );
    storeDupMap1( enode, result );
  }

  Enode * new_formula = valDupMap1( formula );
  doneDupMap1( );

  assert( new_formula );
  return new_formula;
}
//
// After having colored all the assertions,
// some terms could figure as Alocal, but they
// are actually ABcommon. Fix coloring then
//
void Egraph::maximizeColors( )
{
  // cerr << "MAXIMIZE COLORS: " << endl;

  vector< Enode * > unprocessed_enodes;

  for ( list< Enode * >::iterator it = assertions.begin( )
      ; it != assertions.end( )
      ; it ++ )
  {
    unprocessed_enodes.push_back( *it );
  }

  initDup1( );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( isDup1( enode ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; arg_list != enil
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );

      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !isDup1( arg ) )
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

    // If all children are AB, this
    // term has to be considered AB
    // as well
    if ( !enode->isVar( ) 
      && !enode->hasSortBool( ) )
    {
      assert( enode->getIPartitions( ) != 0 );
      ipartitions_t max_inner_parts = 0;
      // Set partitions for symbol
      if ( enode->isUf( ) || enode->isUp( ) )
	max_inner_parts = enode->getCar( )->getIPartitions( );
      // Set symbol is shared everywhere
      else
	max_inner_parts = ~max_inner_parts;
      for ( Enode * arg_list = enode->getCdr( )
	  ; !arg_list->isEnil( )	
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = arg_list->getCar( );
	assert( arg->getIPartitions( ) != 0 );
	max_inner_parts &= arg->getIPartitions( );
      }
      assert( max_inner_parts != 0 );
      enode->addIPartitions( max_inner_parts );
    }

    storeDup1( enode );
  }

  doneDup1( );
}

void Egraph::finalizeColors( Enode * f, const ipartitions_t & partition )
{
  vector< Enode * > unprocessed_enodes;
  unprocessed_enodes.push_back( f );

  initDup1( );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( isDup1( enode ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; arg_list != enil
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );

      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !isDup1( arg ) )
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

    if (  enode->hasSortBool( ) 
      && !enode->isVar( )
      && !enode->isBooleanOperator( )
      && !enode->isUp( ) )
    {
      enode->addIPartitions( partition );
    }

    storeDup1( enode );
  }

  doneDup1( );
}
#endif

//
// Computes the polarities for theory atoms and
// set the decision polarity
// Nodes with both polarities gets a random polarity
//
void Egraph::computePolarities( Enode * formula )
{
  // Polarity will be all true or all false or all random
  if ( config.sat_polarity_mode <= 2 )
    return;

  assert( config.logic != UNDEF );

  vector< Enode * > unprocessed_enodes;
  initDup1( );

  unprocessed_enodes  .push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    unprocessed_enodes  .pop_back( );
    //
    // Skip if the node has already been processed before
    //
    if ( isDup1( enode ) )
      continue;

    //
    // Process children
    //
    if ( enode->isBooleanOperator( ) )
    {
      Enode * arg_list;
      for ( arg_list = enode->getCdr( )
	  ; !arg_list->isEnil( )
	  ; arg_list = arg_list->getCdr( ) )
      {
	Enode * arg = arg_list->getCar( );
	assert( arg->isTerm( ) );
	unprocessed_enodes  .push_back( arg );
      }

      storeDup1( enode );
      continue;
    }

    assert( enode->isAtom( ) );
    //
    // Skip Boolean atoms
    //
    if ( !enode->isTAtom( ) )
      continue;
    //
    // Here set polarity
    //
    if ( config.logic == QF_UF )
    {
      if ( enode->isEq( ) )
      {
	Enode * lhs = enode->get1st( );
	Enode * rhs = enode->get2nd( );
	//
	// Equality between the same f
	//
	if ( lhs->getCar( ) == rhs->getCar( ) )
	  enode->setDecPolarity( l_False );
	else
	  enode->setDecPolarity( l_True );
      }
      else if ( enode->isUp( ) )
	enode->setDecPolarity( l_False );
    }
    //
    // This function assumes polynomes to be canonized
    // in the form a_1 * x_1 + ... + a_n * x_n <= c
    // including difference logic constraints
    //
    else if ( config.logic == QF_IDL
	   || config.logic == QF_RDL
           || config.logic == QF_LRA
           || config.logic == QF_LIA
           || config.logic == QF_UFIDL
           || config.logic == QF_UFLRA)
    {
      if ( enode->isLeq( ) )
      {
	assert( enode->get1st( )->isConstant( )
	     || enode->get2nd( )->isConstant( ) );
	if ( enode->get1st( )->isConstant( ) )
	{
	  const Real & weight = enode->get1st( )->getValue( );
	  enode->setDecPolarity( weight > 0 ? l_True : l_False );
	}
	if ( enode->get2nd( )->isConstant( ) )
	{
	  const Real & weight = enode->get2nd( )->getValue( );
	  enode->setDecPolarity( weight < 0 ? l_True : l_False );
	}
      }
    }

    storeDup1( enode );
  }

  // Done with cache
  doneDup1( );
}

void Egraph::addAssertion( Enode * e )
{
  assert( e );

  if ( config.incremental )
  {
    //
    // Canonize arithmetic and split equalities
    //
    if ( config.logic == QF_IDL
      || config.logic == QF_RDL
      || config.logic == QF_LRA
      || config.logic == QF_LIA
      || config.logic == QF_UFIDL
      || config.logic == QF_UFLRA )
    {
      if ( config.sat_lazy_dtc != 0 )
	e = canonizeDTC( e, true );
      else
	e = canonize( e, true );
    }
    //
    // Booleanize and normalize bitvectors
    //
    else if ( config.logic == QF_BV )
    {
      BVBooleanize booleanizer( *this, config );
      BVNormalize normalizer  ( *this, config );
      e = booleanizer.doit( e );
      e = normalizer .doit( e );
    }
    else
    {
      // warning( "assumption not canonized/normalized" );
    }
  }

  assertions.push_back( e );

#ifdef PRODUCE_PROOF
  // Tag formula for interpolation
  // (might not be necessary, but we do it)
  assert( formulae_to_tag.empty( ) );
  formulae_to_tag.push_back( assertions.back( ) );
  addIFormula( ); 
  formulae_to_tag.clear( );
#endif

  assert( !assertions.empty( ) );
}

Enode * Egraph::canonize( Enode * formula, bool split_eqs )
{
  assert( config.logic != QF_UFIDL || config.sat_lazy_dtc == 0 );
  assert( config.logic != QF_UFLRA || config.sat_lazy_dtc == 0 );

  vector< Enode * > unprocessed_enodes;
  initDupMap1( );

  unprocessed_enodes.push_back( formula );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; arg_list != enil
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( valDupMap1( arg ) == NULL )
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
    Enode * result = NULL;
    //
    // Replace arithmetic atoms with canonized version
    //
    if (  enode->isTAtom( ) 
      && !enode->isUp( ) )
    {
      LAExpression a( enode );
      result = a.toEnode( *this );
      
      if ( split_eqs && result->isEq( ) )
      {
#ifdef PRODUCE_PROOF
	if ( config.produce_inter != 0 )
	  opensmt_error2( "can't compute interpolant for equalities at the moment ", enode );
#endif
	LAExpression aa( enode );
	Enode * e = aa.toEnode( *this );
	Enode * lhs = e->get1st( );
	Enode * rhs = e->get2nd( );
	Enode * leq = mkLeq( cons( lhs, cons( rhs ) ) );
	LAExpression b( leq );
	leq = b.toEnode( *this );
	Enode * geq = mkGeq( cons( lhs, cons( rhs ) ) );
	LAExpression c( geq );
	geq = c.toEnode( *this );
	result = mkAnd( cons( leq, cons( geq ) ) );
      }
    }
    //
    // If nothing have been done copy and simplify
    //
    if ( result == NULL )
      result = copyEnodeEtypeTermWithCache( enode );

    assert( valDupMap1( enode ) == NULL );
    storeDupMap1( enode, result );
  }

  Enode * new_formula = valDupMap1( formula );
  assert( new_formula );
  doneDupMap1( );

  return new_formula;
}

//
// Maximize and/or and simplify if possible
//
Enode * Egraph::maximize( Enode * e )
{
  initDupMap1( );
  vector< Enode * > unprocessed_enodes;

  unprocessed_enodes.push_back( e );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( valDupMap1( arg ) == NULL )
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
    Enode * result = NULL;
    //
    // Maximize and
    //
    if ( enode->isAnd( ) 
      || enode->isOr( ) )
    {
      initDup2( );
      list< Enode * > new_list;

      Enode * arg_list;
      for ( arg_list = enode->getCdr( )
	  ; !arg_list->isEnil( ) && result == NULL
	  ; arg_list = arg_list->getCdr( ) )
      {
	// Retrieve simplified term
	Enode * arg = valDupMap1( arg_list->getCar( ) );

	if ( ( enode->isAnd( ) && arg->isAnd( ) )
	  || ( enode->isOr ( ) && arg->isOr ( ) ) )
	{
	  Enode * arg_arg_list;
	  for ( arg_arg_list = arg->getCdr( )
	      ; !arg_arg_list->isEnil( ) && result == NULL
	      ; arg_arg_list = arg_arg_list->getCdr( ) )
	  {
	    // cerr << "arg_arg_list car: " << arg_arg_list->getCar( ) << endl;
	    // cerr << "              id: " << arg_arg_list->getCar( )->getId( ) << endl;
	    // Retrieve simplified term
	    // Enode * arg_arg = valDupMap1( arg_arg_list->getCar( ) );
	    Enode * arg_arg = arg_arg_list->getCar( );
	    assert( arg_arg );
	    // cerr << "arg_arg: " << arg_arg << endl;

	    // Skip duplicates
	    if ( isDup2( arg_arg ) )
	      continue;

	    if ( arg_arg->isTrue( ) )
	    {
	      // Skip uninfluent
	      if ( enode->isAnd( ) )
		continue;
	      // It's true
	      else
		result = mkTrue( );
	    }
	    else if ( arg_arg->isFalse( ) )
	    {
	      // Skip uninfluent
	      if ( enode->isOr( ) )
		continue;
	      // It's false
	      else
		result = mkFalse( );
	    }

	    /*
	     * Causes problems as it creates new nodes
	     *
	    // !arg was processed before ... 	
	    if ( !arg->isNot( ) 
	      && isDup2( mkNot( cons( arg ) ) ) )
	    {
	      if ( enode->isOr( ) )
		result = mkTrue( );
	      else
		result = mkFalse( );
	    }
	    */

	    // arg was processed before ... 	
	    if ( arg_arg->isNot( ) 
	      && isDup2( arg_arg->get1st( ) ) )
	    {
	      if ( enode->isOr( ) )
		result = mkTrue( );
	      else
		result = mkFalse( );
	    }

	    storeDup2( arg_arg );
	    new_list.push_front( arg_arg );
	  }
	}
	else
	{
	  // Skip duplicates
	  if ( isDup2( arg ) )
	    continue;

	  if ( arg->isTrue( ) )
	  {
	    // Skip uninfluent
	    if ( enode->isAnd( ) )
	      continue;
	    // It's true
	    else
	      result = mkTrue( );
	  }
	  else if ( arg->isFalse( ) )
	  {
	    // Skip uninfluent
	    if ( enode->isOr( ) )
	      continue;
	    // It's false
	    else
	      result = mkFalse( );
	  }

	  /*
	   * Causes problems as it creates new nodes
	   *
	  // !arg was processed before ... 	
	  if ( !arg->isNot( ) 
	  && isDup2( mkNot( cons( arg ) ) ) )
	  {
	  if ( enode->isOr( ) )
	  result = mkTrue( );
	  else
	  result = mkFalse( );
	  }
	  */

	  // arg was processed before ... 	
	  if ( arg->isNot( ) 
	      && isDup2( arg->get1st( ) ) )
	  {
	    if ( enode->isOr( ) )
	      result = mkTrue( );
	    else
	      result = mkFalse( );
	  }

	  storeDup2( arg );
	  new_list.push_front( arg );
	}
      }

      doneDup2( );

      if ( result == NULL )
	result = cons( enode->getCar( )
	       , cons( new_list ) );

      // cerr << "Processed: " << enode << endl;
      // cerr << "   Result: " << result << endl;
    }
    else 
    {
      result = copyEnodeEtypeTermWithCache( enode );
    }

    assert( valDupMap1( enode ) == NULL );
    storeDupMap1( enode, result );

    // cerr << "Saving result at id: " << enode->getId( ) << endl;
  }

  Enode * new_e = valDupMap1( e );
  assert( new_e );
  doneDupMap1( );

  return new_e;
}

#ifndef SMTCOMP
//
// Functions for evaluating an expression
//
void Egraph::evaluateTerm( Enode * e, Real & v )
{
  assert( model_computed );
  assert( e->hasSortReal( ) );
  // Recursively compute value
  evaluateTermRec( e, v );
}

void Egraph::evaluateTermRec( Enode * e, Real & v )
{
  assert( false );
  //
  // Base cases
  //
  if ( e->isConstant( ) )
  {
    v = e->getValue( );
  }
  else if ( e->isVar( ) )
  {
    if ( !e->hasValue( ) )
      opensmt_error2( "cannot determine value for ", e );

    v = e->getValue( );
  }
  else
  {
    Real a, b = 0;
    if ( e->isPlus( ) )
    {
      Enode * l;
      for ( l = e->getCdr( )
	  ; !l->isEnil( )
	  ; l = l->getCdr( ) )
      {
	evaluateTermRec( l->getCar( ), a );
	b += a;
      }
      v = b;
    }
    else if ( e->isTimes( ) )
    {
      b = 1;
      Enode * l;
      for ( l = e->getCdr( )
	  ; !l->isEnil( )
	  ; l = l->getCdr( ) )
      {
	evaluateTermRec( l->getCar( ), a );
	b *= a;
      }
      v = b;
    }
    else if ( e->isUminus( ) )
    {
      evaluateTermRec( e->get1st( ), a );
      v = -a;
    }
    else if ( e->isMinus( ) )
    {
      evaluateTermRec( e->get1st( ), a );
      evaluateTermRec( e->get2nd( ), b );
      v = a - b;
    }
    else
    {
      opensmt_error2( "operator not handled (yet) ", e->getCar( ) );
    }
  }
}
#endif

#ifdef PRODUCE_PROOF
void Egraph::addIFormula( )
{
  // tagIFormulae( SETBIT( iformula ) );
  ipartitions_t partition = 0;
  setbit( partition, iformula );
  tagIFormulae( partition );
  iformula ++;
  /*
  if ( iformula == 63 )
    opensmt_error( "currently only up to 62 partitions are allowed" );
  */
}

void Egraph::tagIFormulae( const ipartitions_t & partitions )
{
  if ( config.produce_inter == 0 )
    return;
  assert( partitions != 0 );
  assert( !automatic_coloring );
  tagIFormulae( partitions, formulae_to_tag );
}

void Egraph::tagIFormulae( const ipartitions_t & partitions
                         , vector< Enode * > & f_to_tag )
{
  if ( config.produce_inter == 0 )
    return;
  assert( !automatic_coloring );

  initDup1( );
  while( !f_to_tag.empty( ) )
  {
    Enode * enode = f_to_tag.back( );

    if ( isDup1( enode ) )
    {
      f_to_tag.pop_back( );
      continue;
    }

    bool unprocessed_children = false;

    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( !isDup1( arg ) )
      {
	f_to_tag.push_back( arg );
	unprocessed_children = true;
      }
    }
    //
    // SKip if unprocessed_children
    //
    if ( unprocessed_children )
      continue;

    f_to_tag.pop_back( );

    // Tag only up to predicates
    if ( !enode->isBooleanOperator( ) )
      enode->addIPartitions( partitions );
    // Tag symbol as well ...
    if ( enode->isUf( ) || enode->isUp( ) )
      enode->getCar( )->addIPartitions( partitions );

    storeDup1( enode );
  }

  doneDup1( );
}

void
Egraph::tagIFormula( Enode * e, const ipartitions_t & partitions )
{
  assert( !automatic_coloring );
  vector< Enode * > f_to_tag;
  f_to_tag.push_back( e );
  tagIFormulae( partitions, f_to_tag );
}
#endif

Enode * Egraph::mkLet( Enode * t )
{
  initDupMap1( );
  vector< Enode * > unprocessed_enodes;

  unprocessed_enodes.push_back( t );
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( valDupMap1( enode ) != NULL )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; arg_list != enil
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( valDupMap1( arg ) == NULL )
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
    Enode * result = NULL;
    //
    // Replace with corresponding definition
    //
    if ( enode->isDef( ) )
      result = enode->getDef( );
    else 
      result = copyEnodeEtypeTermWithCache( enode );

    assert( valDupMap1( enode ) == NULL );
    storeDupMap1( enode, result );
  }

  Enode * new_t = valDupMap1( t );
  assert( new_t );
  doneDupMap1( );

  return new_t;
}

//=================================================================================================
// Debugging Routines

#ifdef STATISTICS
void Egraph::printMemStats( ostream & os )
{
  unsigned total = 0;

  for ( unsigned i = 0 ; i < id_to_enode.size( ) ; i ++ )
  {
    Enode * e = id_to_enode[ i ];
    assert( e != NULL );
    total += e->sizeInMem( );
  }

  os << "# " << endl;
  os << "# General Statistics" << endl;
  os << "#" << endl;
  os << "# Total enodes..........: " << id_to_enode.size( ) << endl;
  os << "# Enode size in memory..: " << ( total / 1048576.0 ) << " MB" << endl;
  os << "# Avg size per enode....: " << ( total / id_to_enode.size( ) ) << " B" << endl;
  os << "#" << endl;
  os << "# Splay Tree Statistics" << endl;
  store.printStatistics( os );
  os << "#" << endl;
  os << "# Signature Table Statistics" << endl;
  enodeid_t maximal;
  sig_tab.printStatistics( os, &maximal );
  os << "# Maximal node..........: " << id_to_enode[ maximal ] << endl;
  os << "#" << endl;
  os << "# Supporting data structures" << endl;
  os << "#" << endl;
  os << "# id_to_enode........: " << id_to_enode.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
  os << "# duplicates1........: " << duplicates1.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "# duplicates2........: " << duplicates2.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "# dup_map1...........: " << dup_map1.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
  os << "# dup_set1...........: " << dup_set1.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "# dup_map2...........: " << dup_map2.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
  os << "# dup_set2...........: " << dup_set2.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "# id_to_belong_mask..: " << id_to_belong_mask.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "# id_to_fan_in.......: " << id_to_fan_in.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "# index_to_dist......: " << index_to_dist.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
  os << "# cache..............: " << cache.size( ) * sizeof( Enode * ) / 1048576.0 << " MB" << endl;
  os << "# ext_store..........: " << ext_store.size( ) * sizeof( pair< pair< int, int >, Enode * > ) / 1048576.0 << " MB" << endl;
  os << "# se_store...........: " << se_store.size( ) * sizeof( pair< pair< int, int >, Enode * > ) / 1048576.0 << " MB" << endl;
  os << "# id_to_inc_edges....: " << id_to_inc_edges.size( ) * sizeof( int ) / 1048576.0 << " MB" << endl;
  os << "#" << endl;

}

void Egraph::printEnodeList( ostream & os )
{
  os << "# =================================================" << endl;
  os << "# Enode Bank Information" << endl;
  os << "# " << endl;
  os << "# -----+-------------------------------------------" << endl;
  os << "# Enode Symbol List" << endl;
  os << "# -----+-------------------------------------------" << endl;
  for ( unsigned i = 0 ; i < id_to_enode.size( ) ; i ++ )
  {
    Enode * e = id_to_enode[ i ];

    if( e->getId( ) <= ENODE_ID_LAST )
      continue;

    if( e->isSymb( ) || e->isNumb( ) || e->isDef( ) )
    {
      // Print index formatted
      stringstream tmp; tmp << i;
      os << "# ";
      for ( int j = 3 - tmp.str( ).size( ) ; j >= 0 ; j -- ) os << " ";
      os << tmp.str( ) << " | ";

      e->print( os );
      os << endl;
    }
  }
  os << "# -----+-------------------------------------------" << endl;
  os << "# Enode Term List" << endl;
  os << "# -----+-------------------------------------------" << endl;
  for ( unsigned i = 0 ; i < id_to_enode.size( ) ; i ++ )
  {
    Enode * e = id_to_enode[ i ];
    if( e->isTerm( ) )
    {
      // Print index formatted
      stringstream tmp; tmp << i;
      os << "# ";
      for ( int j = 3 - tmp.str( ).size( ) ; j >= 0 ; j -- ) os << " ";
      os << tmp.str( ) << " | ";

      e->print( os );
      os << endl;
    }
  }
  os << "# -----+-------------------------------------------" << endl;
  os << "# Enode List List" << endl;
  os << "# -----+-------------------------------------------" << endl;
  for ( unsigned i = 0 ; i < id_to_enode.size( ) ; i ++ )
  {
    Enode * e = id_to_enode[ i ];
    if( e->isList( ) )
    {
      // Print index formatted
      stringstream tmp; tmp << i;
      os << "# ";
      for ( int j = 3 - tmp.str( ).size( ) ; j >= 0 ; j -- ) os << " ";
      os << tmp.str( ) << " | ";

      e->print( os );
      os << endl;
    }
  }
}
#endif

void Egraph::dumpAssertionsToFile( const char * filename )
{
  ofstream dump_out ( filename );
  dumpHeaderToFile  ( dump_out );
  dump_out << endl;
  for ( list< Enode * >::const_iterator ass_it = assertions.begin();
        ass_it != assertions.end();
        ++ass_it) {
    dumpFormulaToFile ( dump_out, *ass_it );
  }
  dump_out << "(check-sat)" << endl;
  dump_out << "(exit)" << endl;
  dump_out.close( );
  cerr << "[Dumped " << filename << "]" << endl;
}

void Egraph::dumpToFile( const char * filename, Enode * formula )
{
  ofstream dump_out ( filename );
  dumpHeaderToFile  ( dump_out );
  dump_out << endl;
  dumpFormulaToFile ( dump_out, formula );
  dump_out << "(check-sat)" << endl;
  dump_out << "(exit)" << endl;
  dump_out.close( );
  cerr << "[Dumped " << filename << "]" << endl;
}

void Egraph::dumpHeaderToFile( ostream & dump_out, logic_t l )
{
  if ( l == UNDEF ) l = config.logic;
  dump_out << "(set-logic " << logicStr( l ) << ")" << endl;
  dump_out << "(set-info :source |" << endl
           << "Dumped with " 
           << PACKAGE_STRING
	   << " on " 
	   << __DATE__ << "." << endl
	   << "For info contact Roberto Bruttomesso <roberto.bruttomesso@gmail.com>" << endl
	   << "|)"
	   << endl;
  dump_out << "(set-info :smt-lib-version 2.0)" << endl;
  // Dump sorts
  sort_store.dumpSortsToFile( dump_out );
  // Dump function declarations
  for ( map< string, Enode * >::iterator it = name_to_symbol.begin( )
      ; it != name_to_symbol.end( ) 
      ; it ++ )
  {
    Enode * s = it->second;
    // Skip predefined/parametric symbols
    if ( s->getId( ) <= ENODE_ID_LAST 
      || s->getName( ) == string( "select" )
      || s->getName( ) == string( "store" ) 
      || s->getName( ) == string( "diff" ) 
      || s->getName( ) == string( "fake_interp" ) 
      || s->getName( ) == string( "ite" ) )
      continue;
    dump_out << "(declare-fun " << s->getName( ) << " ";
    if ( s->getArgSort( ) )
      dump_out << s->getArgSort( ); 
    else
      dump_out << "()";
    dump_out << " " << s->getRetSort( ) << ")" << endl;
  }
}

#define COMPACT_BOOLEANS_ONLY 1

void Egraph::dumpFormulaToFile( ostream & dump_out, Enode * formula, bool negate )
{
  vector< Enode * > unprocessed_enodes;
  map< enodeid_t, string > enode_to_def;

  unprocessed_enodes.push_back( formula );
  // Open assert and let
  dump_out << "(assert" << endl;
  dump_out << "(let ("; 
  //
  // Visit the DAG of the formula from the leaves to the root
  //
  while( !unprocessed_enodes.empty( ) )
  {
    Enode * enode = unprocessed_enodes.back( );
    //
    // Skip if the node has already been processed before
    //
    if ( enode_to_def.find( enode->getId( ) ) != enode_to_def.end( ) )
    {
      unprocessed_enodes.pop_back( );
      continue;
    }

    bool unprocessed_children = false;
    Enode * arg_list;
    for ( arg_list = enode->getCdr( )
	; !arg_list->isEnil( )
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->isTerm( ) );
      //
      // Push only if it is unprocessed
      //
      if ( enode_to_def.find( arg->getId( ) ) == enode_to_def.end( )
#if COMPACT_BOOLEANS_ONLY
	&& arg->isBooleanOperator( ) 
#endif
	)
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

    char buf[ 32 ];
    sprintf( buf, "?def%d", enode->getId( ) );

    // Open binding
    dump_out << "(" << buf << " ";

    if ( enode->getArity( ) > 0 ) 
      dump_out << "(";
    dump_out << enode->getCar( );
    for ( Enode * list = enode->getCdr( )
	; !list->isEnil( )
	; list = list->getCdr( ) )
    {
      Enode * arg = list->getCar( );
#if COMPACT_BOOLEANS_ONLY
      if ( arg->isBooleanOperator( ) )
#endif
	dump_out << " " << enode_to_def[ arg->getId( ) ];
#if COMPACT_BOOLEANS_ONLY
      else
      {
	dump_out << " " << arg;
	if ( enode->isAnd( ) )
	  dump_out << endl;
      }
#endif
    }
    if ( enode->getArity( ) > 0 ) dump_out << ")";
    
    // Closes binding
    dump_out << ")" << endl;

    assert( enode_to_def.find( enode->getId( ) ) == enode_to_def.end( ) );
    enode_to_def[ enode->getId( ) ] = buf;
  }

  // Closes binding list
  dump_out << ")" << endl;
  // Formula
  if ( negate ) dump_out << "(not ";
  dump_out << enode_to_def[ formula->getId( ) ] << endl;
  if ( negate ) dump_out << ")";
  // Close let
  dump_out << ")";
  // Closes assert
  dump_out << ")" << endl;
}
