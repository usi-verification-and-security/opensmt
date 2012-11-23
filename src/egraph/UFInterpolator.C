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

#ifdef PRODUCE_PROOF

#include "UFInterpolator.h"
#include "Egraph.h"

void CGraph::addCNode( Enode * e )
{
  assert( e );
  map< enodeid_t, CNode * >::iterator it = cnodes_store.find( e->getId( ) );
  if ( it != cnodes_store.end( ) ) return;
  CNode * n = new CNode( e->getId( ), e );
  cnodes_store[ e->getId( ) ] = n;
  cnodes.push_back( n );
  // We need to color this node. It might
  // be a result from some congruence
  // closure operations, hence it might be
  // uncolored
  if ( e->getIPartitions( ) == 0 )
  {
    ipartitions_t max_inner_parts = 0;
    // Set partitions for symbol
    if ( e->isUf( ) )
      max_inner_parts = e->getCar( )->getIPartitions( );
    // Set symbol is shared everywhere
    else
      max_inner_parts = ~max_inner_parts;

    for ( Enode * arg_list = e->getCdr( )
	; !arg_list->isEnil( )	
	; arg_list = arg_list->getCdr( ) )
    {
      Enode * arg = arg_list->getCar( );
      assert( arg->getIPartitions( ) != 0 );
      max_inner_parts &= arg->getIPartitions( );
    }
    assert( max_inner_parts != 0 );
    e->setIPartitions( max_inner_parts );
  }
  assert( e->getIPartitions( ) != 0 );
}

void CGraph::colorNodes( const ipartitions_t & mask )
{
  for ( size_t i = 0 ; i < cnodes.size( ) ; i ++ )
    colorNodesRec( cnodes[ i ], mask );
}

icolor_t CGraph::colorNodesRec( CNode * c, const ipartitions_t & mask )
{
  assert( c->e->getIPartitions( ) != 0 );

  // Already done
  if ( colored_nodes.find( c ) != colored_nodes.end( ) )
    return c->color;

  icolor_t color = I_UNDEF;

  if ( c->e->isUp( ) )
  {
    opensmt_error( "Cannot compute interpolants for uninterpreted predicates, sorry" );

    // Predicate symbol: color depending on the arguments
    // Decide color of term as intersection
    color = I_AB;
    assert( c->e->getCar( )->getIPartitions( ) != 0 );

    if ( isAstrict( c->e->getCar( )->getIPartitions( ), mask ) )
      color = I_A;
    else if ( isBstrict( c->e->getCar( )->getIPartitions( ), mask ) )
      color = I_B;

    Enode * args = c->e->getCdr( );
    for ( args = c->e->getCdr( ) 
	; !args->isEnil( )
	; args = args->getCdr( ) )
    {
      Enode * arg = args->getCar( );
      // Not necessairily an argument is needed in the graph
      if ( cnodes_store.find( arg->getId( ) ) != cnodes_store.end( ) )
	color = static_cast< icolor_t >( color & colorNodesRec( cnodes_store[ arg->getId( ) ], mask ) );
    }
  }
  else if ( isAB( c->e->getIPartitions( ), mask ) )
  {
    color = I_AB;
  }
  else if ( isAstrict( c->e->getIPartitions( ), mask ) )
  {
    color = I_A;
  }
  else
  {
    assert( isBstrict( c->e->getIPartitions( ), mask ) );
    color = I_B;
  }

  c->color = color;

  Enode * args = c->e->getCdr( );
  for ( args = c->e->getCdr( ) 
      ; !args->isEnil( )
      ; args = args->getCdr( ) )
  {
    Enode * arg = args->getCar( );
    // Not necessairily an argument is needed in the graph
    if ( cnodes_store.find( arg->getId( ) ) != cnodes_store.end( ) )
      colorNodesRec( cnodes_store[ arg->getId( ) ], mask );
  }

  assert( c->color == I_A 
       || c->color == I_B 
       || c->color == I_AB );

  assert( colored_nodes.find( c ) == colored_nodes.end( ) );
  colored_nodes.insert( c );

  return c->color;
}

void CGraph::addCEdge( Enode * s, Enode * t, Enode * r )
{
  assert( s );
  assert( t );
  // Retrieve corresponding nodes
  CNode * cs = cnodes_store[ s->getId( ) ];
  CNode * ct = cnodes_store[ t->getId( ) ];
  // Create edge
  CEdge * edge = new CEdge( cs, ct, r );
  // Storing edge in cs and ct
  assert( cs->next == NULL ); 
  cs->next = edge;
  cedges.push_back( edge ); 
}

void CGraph::color( const ipartitions_t & mask )
{
  assert( conf1 );
  assert( conf2 );
  // Starting from
  CNode * c1 = cnodes_store[ conf1->getId( ) ]; 
  CNode * c2 = cnodes_store[ conf2->getId( ) ]; 
  assert( !colored );
  assert( colored_nodes.empty( ) );
  // Color nodes
  colorNodes( mask );

  // Uncomment to print
  // ofstream nout( "nodecol_graph.dot" );
  // printAsDotty( nout );
  // cerr << "[Dumped nodecol_graph.dot]" << endl;

  // Edges can be colored as consequence of nodes
  const bool no_mixed = colorEdges( c1, c2, mask );
  if ( !no_mixed ) return;

  // Uncomment to print
  // ofstream eout( "edgecol_graph.dot" );
  // printAsDotty( eout );
  // cerr << "[Dumped edgecol_graph.dot]" << endl;

  // Check colors
  assert( checkColors( ) );

  // Graph is now colored
  colored = true;
}

void CGraph::colorReset( )
{
  // Decolor nodes
  for ( set< CNode * >::iterator it = colored_nodes.begin( )
      ; it != colored_nodes.end( )
      ; it ++ )
  {
    (*it)->color = I_UNDEF;
  }
  colored_nodes.clear( );

  // Decolor edges
  for ( set< CEdge * >::iterator it = colored_edges.begin( )
      ; it != colored_edges.end( )
      ; it ++ )
  {
    (*it)->color = I_UNDEF;
  }
  colored_edges.clear( );

  // Undo adjustments
  while( !undo_adjust.empty( ) )
  {
    CAdjust * adj = undo_adjust.back( );
    undo_adjust.pop_back( );
    adj->undo( );
    delete adj;
  }

  // Clear processed paths
  path_seen.clear( );

  colored = false;
}

#define ITERATIVE_COLORING 1

#if ITERATIVE_COLORING
bool CGraph::colorEdges( CNode * c1
                       , CNode * c2
		       , const ipartitions_t & mask )
{
  set< pair< CNode *, CNode * > > cache_nodes;
  set< CEdge * > cache_edges;
  // set< pair< CNode *, CNode * > > already_on_stack;
  vector< CNode * > unprocessed_nodes;
  unprocessed_nodes.push_back( c1 );
  unprocessed_nodes.push_back( c2 );
  bool no_mixed = true;

  while ( !unprocessed_nodes.empty( ) && no_mixed )
  {
    assert( unprocessed_nodes.size( ) % 2 == 0 );
    CNode * n1 = unprocessed_nodes[ unprocessed_nodes.size( ) - 2 ];
    CNode * n2 = unprocessed_nodes[ unprocessed_nodes.size( ) - 1 ];
    //
    // Skip if path already seen
    //
    if ( cache_nodes.find( make_pair( n1, n2 ) ) != cache_nodes.end( ) )
    {
      unprocessed_nodes.pop_back( );
      unprocessed_nodes.pop_back( );
      continue;
    }
    //
    // Push congruence children otherwise
    //
    bool unprocessed_children = false;
    // Direction n1 ----> n2
    CNode * x = n1;
    while( x->next != NULL )
    {
      //
      // Consider only sub-paths with congruence edges
      // Congruence edge is the first time we see
      //
      if ( x->next->reason == NULL 
	&& cache_edges.insert( x->next ).second )
      {
	CNode * n = x->next->target;
	assert( x->e->getArity( ) == n->e->getArity( ) );
	Enode * arg_list_x, * arg_list_n;
	// Iterate over function's arguments
	for ( arg_list_x = x->e->getCdr( )
	    , arg_list_n = n->e->getCdr( )
	    ; !arg_list_x->isEnil( ) 
	    ; arg_list_x = arg_list_x->getCdr( )
	    , arg_list_n = arg_list_n->getCdr( ) )
	{
	  Enode * arg_x = arg_list_x->getCar( );
	  Enode * arg_n = arg_list_n->getCar( );

	  if ( arg_x == arg_n ) continue;

	  CNode * arg_n1 = cnodes_store[ arg_x->getId( ) ];
	  CNode * arg_n2 = cnodes_store[ arg_n->getId( ) ];
	  // Push only unprocessed paths
	  if ( cache_nodes.find( make_pair( arg_n1, arg_n2 ) ) == cache_nodes.end( ) )
	    // && !already_on_stack.insert( make_pair( arg_n1, arg_n2 ) ).second )
	  {
	    unprocessed_nodes.push_back( arg_n1 );
	    unprocessed_nodes.push_back( arg_n2 );
	    unprocessed_children = true;
	  }
	}
      }
      x = x->next->target;
    }
    // Direction n1 <--- n2
    x = n2;
    while( x->next != NULL )
    {
      // Consider only sub-paths with congruence edges
      if ( x->next->reason == NULL 
	&& cache_edges.insert( x->next ).second )
      {
	CNode * n = x->next->target;
	assert( x->e->getArity( ) == n->e->getArity( ) );
	Enode * arg_list_x, * arg_list_n;
	// Iterate over function's arguments
	for ( arg_list_x = x->e->getCdr( )
	    , arg_list_n = n->e->getCdr( )
	    ; !arg_list_x->isEnil( ) 
	    ; arg_list_x = arg_list_x->getCdr( )
	    , arg_list_n = arg_list_n->getCdr( ) )
	{
	  Enode * arg_x = arg_list_x->getCar( );
	  Enode * arg_n = arg_list_n->getCar( );

	  if ( arg_x == arg_n ) continue;

	  CNode * arg_n1 = cnodes_store[ arg_x->getId( ) ];
	  CNode * arg_n2 = cnodes_store[ arg_n->getId( ) ];
	  // Push only unprocessed paths
	  if ( cache_nodes.find( make_pair( arg_n1, arg_n2 ) ) == cache_nodes.end( ) )
	    // && !already_on_stack.insert( make_pair( arg_n1, arg_n2 ) ).second )
	  {
	    unprocessed_nodes.push_back( arg_n1 );
	    unprocessed_nodes.push_back( arg_n2 );
	    unprocessed_children = true;
	  }
	}
      }
      x = x->next->target;
    }
    //
    // Color children first
    //
    if ( unprocessed_children )
      continue;

    //
    // Otherwise remove this pair
    //
    unprocessed_nodes.pop_back( );
    unprocessed_nodes.pop_back( );
    //
    // Color this path
    //
    no_mixed = colorEdgesFrom( n1, mask )
            && colorEdgesFrom( n2, mask );
    //
    // Remember this path is done
    //
    cache_nodes.insert( make_pair( n1, n2 ) );
  }

  return no_mixed;
}
#else
bool CGraph::colorEdges( CNode * c1
                       , CNode * c2
		       , const ipartitions_t & mask )
{
  return colorEdgesRec( c1, c2, mask );
}

bool CGraph::colorEdgesRec( CNode * c1
                          , CNode * c2
			  , const ipartitions_t & mask )
{
  return colorEdgesFrom( c1, mask )
      && colorEdgesFrom( c2, mask );
}
#endif

// 
// It assumes that children have been already colored
// and adjusted
//
bool CGraph::colorEdgesFrom( CNode * x, const ipartitions_t & mask )
{
  assert( x );

  // Color from x
  CNode * n = NULL;

  while( x->next != NULL 
      && x->next->color == I_UNDEF )
  {
    n = x->next->target;

    // Congruence edge, recurse on arguments
    if ( x->next->reason == NULL )
    {
      assert( x->e->getArity( ) == n->e->getArity( ) );
#if ITERATIVE_COLORING
#else
      // Color children of the congruence relation, and
      // introduce intermediate nodes if necessary
      Enode * arg_list_x, * arg_list_n;
      for ( arg_list_x = x->e->getCdr( )
	  , arg_list_n = n->e->getCdr( )
	  ; !arg_list_x->isEnil( ) 
	  ; arg_list_x = arg_list_x->getCdr( )
	  , arg_list_n = arg_list_n->getCdr( ) )
      {
	Enode * arg_x = arg_list_x->getCar( );
	Enode * arg_n = arg_list_n->getCar( );
	if ( arg_x == arg_n ) continue;

	// Check that path has not been considered yet
	if ( !path_seen.insert( make_pair( arg_x, arg_n ) ).second )
	  continue;

	// Call recursively on arguments
	colorEdgesRec( cnodes_store[ arg_x->getId( ) ]
	             , cnodes_store[ arg_n->getId( ) ] 
		     , mask );	
      }
#endif
      // Incompatible colors: this is possible
      // for effect of congruence nodes: adjust
      if ( (x->color == I_A && n->color == I_B)
	|| (x->color == I_B && n->color == I_A) )
      {
	// Need to introduce auxiliary nodes and edges
	// For each argument, find node that is equivalent
	// and of shared color
	list< Enode * > new_args;
	Enode * arg_list_x, * arg_list_n;
	for ( arg_list_x = x->e->getCdr( )
	    , arg_list_n = n->e->getCdr( )
	    ; !arg_list_x->isEnil( ) 
	    ; arg_list_x = arg_list_x->getCdr( )
	    , arg_list_n = arg_list_n->getCdr( ) )
	{
	  Enode * arg_x = arg_list_x->getCar( );
	  Enode * arg_n = arg_list_n->getCar( );

	  // If same node, keep
	  if ( arg_x == arg_n )
	  {
	    new_args.push_front( arg_x );
	  } 
	  else
	  {
	    assert( cnodes_store.find( arg_x->getId( ) ) != cnodes_store.end( ) );
	    assert( cnodes_store.find( arg_n->getId( ) ) != cnodes_store.end( ) );
	    CNode * cn_arg_x = cnodes_store[ arg_x->getId( ) ];
	    CNode * cn_arg_n = cnodes_store[ arg_n->getId( ) ];
	    // There is either a path from arg_x to ABcommon
	    // or a path from arg_n to ABcommon (or both)
	    assert( cn_arg_x->next != NULL
		 || cn_arg_n->next != NULL );

	    // If argument of x is incompatible with n
	    if ( ((cn_arg_x->color & n->color) == 0) )
	    {
	      // Browse the eq-class of cn_arg_x and find an ABcommon symbol
	      Enode * v = arg_x;
	      Enode * abcommon = NULL;
	      const Enode * vstart = v;
	      for ( ; abcommon == NULL ; )
	      {
		v = v->getNext( );
		if ( isAB( v->getIPartitions( ), mask ) ) abcommon = v;
		if ( v == vstart ) break;
	      }
	      assert( abcommon != NULL );
	      assert( cnodes_store.find( abcommon->getId( ) ) != cnodes_store.end( ) );
	      CNode * new_arg_x = cnodes_store[ abcommon->getId( ) ];
	      assert( new_arg_x->color == I_AB );
	      new_args.push_front( abcommon );
	    }
	    // If argument of n is incompatible with x
	    else if ( ((cn_arg_n->color & x->color) == 0) )
	    {
	      // Browse the eq-class of cn_arg_x and find an ABcommon symbol
	      Enode * v = arg_n;
	      Enode * abcommon = NULL;
	      const Enode * vstart = v;
	      for ( ; abcommon == NULL ; )
	      {
		v = v->getNext( );
		if ( isAB( v->getIPartitions( ), mask ) ) abcommon = v;
		if ( v == vstart ) break;
	      }
	      assert( abcommon != NULL );
	      assert( cnodes_store.find( abcommon->getId( ) ) != cnodes_store.end( ) );
	      CNode * new_arg_n = cnodes_store[ abcommon->getId( ) ];
	      assert( new_arg_n->color == I_AB );
	      new_args.push_front( abcommon );
	    }
	    else
	    {
	      opensmt_error( "something went wrong" );
	    }
	    // New arguments must be shared
	    assert( cnodes_store[ new_args.front( )->getId( ) ]->color == I_AB );
	  }
	}
	Enode * na = egraph.cons( new_args );
	Enode * s = x->e->getCar( );
	// nn is the node that can be connected to x and n
	Enode * nn = egraph.cons( s, na );

	// There are two cases now. It is possible
	// that nn is equal to either x or n
	assert( nn != x->e );
	assert( nn != n->e );

	// Adds corresponding node
	addCNode( nn );
	// Remember this
	assert( x->next->target == n );
	CNode * cnn = cnodes.back( );

	// Save for later undo
	CAdjust * adj = new CAdjust( cnn, x, n, x->next );
	undo_adjust.push_back( adj );

	cnn->color = I_AB;
	// Situation x --> n | then make x --> nn
	x->next = NULL;
	addCEdge( x->e, nn, NULL );
	assert( x->next->target == cnn );
	// Choose a color
	assert( x->color == I_A 
	    || x->color == I_B 
	    || x->color == I_AB );

	if ( x->color == I_AB )
	{
	  // McMillan: set AB as B
	  if ( config.proof_set_inter_algo == 0 )
	    cedges.back( )->color = I_B;
	  // McMillan: set AB as A
	  else if ( config.proof_set_inter_algo == 2 )
	    cedges.back( )->color = I_A;
	  // Pudlak: who cares
	  else if ( config.proof_set_inter_algo == 1 )
	    cedges.back( )->color = I_A;
	}
	else
	  cedges.back( )->color = x->color;

	addCEdge( nn, n->e, NULL );	
	cedges.back( )->color = n->color;
	x = cnn;
      }
      // Now all the children are colored, we can decide how to color this
      if ( x->color == n->color )
      {
	// False alarm here is not possible
	assert( x->color );
	// Choose correct color
	if ( x->color == I_AB )
	{
	  // McMillan: set AB as B
	  if ( config.proof_set_inter_algo == 0 )
	    x->next->color = I_B;
	  // McMillan: set AB as A
	  else if ( config.proof_set_inter_algo == 2 )
	    x->next->color = I_A;
	  // Pudlak: who cares
	  else if ( config.proof_set_inter_algo == 1 )
	    x->next->color = I_A;
	}
	// Color with proper color
	else
	  x->next->color = x->color;
      }
      // Different colors: choose intersection
      else
      {
	// It is not possible that are incompatible
	assert( x->color != I_A || n->color != I_B );
	assert( x->color != I_B || n->color != I_A );
	x->next->color = static_cast< icolor_t >( x->color & n->color );
	assert( x->next->color == I_A 
	     || x->next->color == I_B );
      }
    }
    // Color basic edge with proper color
    else 
    {
      // cerr << "Coloring edge: " << x->next->reason << endl;
      // cerr << "        parts: " << x->next->reason->getIPartitions( ) << endl;
      // cerr << "         mask: " << mask << endl;

      const ipartitions_t & p = x->next->reason->getIPartitions( );
      if ( isABmixed( p ) )
	return false;
      else if ( isAstrict( p, mask ) )
	x->next->color = I_A;
      else if ( isBstrict( p, mask ) )
	x->next->color = I_B;
      else 
      {
	assert( isAB( p, mask ) );
	// McMillan: set AB as B
	if ( config.proof_set_inter_algo == 0 )
	  x->next->color = I_B;
	// McMillan: set AB as A
	else if ( config.proof_set_inter_algo == 2 )
	  x->next->color = I_A;
	// Pudlak: who cares
	else if ( config.proof_set_inter_algo == 1 )
	  x->next->color = I_A;
      }
    }
    // This edge has been colored
    colored_edges.insert( x->next );
    // Color must be a power of 2
    assert( x->next->color == I_A || x->next->color == I_B );
    assert( x->next->color != I_A || x->next->color != I_B );
    // Pass to next node
    x = n;
  }

  // No abmixed if here
  return true;
}

//
// Revert path starting from x, if 
// any outgoing edge is present
//
void CGraph::revertEdges( CNode * x )
{
  if ( x->next == NULL )
    return;
  // It has outgoing edge: rewrite 
  CNode * p = x;
  CEdge * prev = p->next;
  while ( prev != NULL )
  {
    // Next is the connecting edge to reverse
    CEdge * next = prev;
    assert( next->source == p );
    // from | p -- next --> t | to | p <-- next -- t
    CNode * t = next->target;
    // Adapt data structures
    next->source = t;
    next->target = p; 
    prev = t->next;
    t->next = next;
    // Next step
    p = t; 
  }
  x->next = NULL;
}

//
// Here mask is a bit-mask of the form 1..10..0
// which indicates the current splitting for the
// formula into A and B.
//
Enode * CGraph::getInterpolant( const ipartitions_t & mask )
{
  assert( !colored );
  color( mask );

  if ( !colored )
  {
    colorReset( );
    assert( !colored );
    return egraph.mkFakeInterp( );
  }

  assert( colored );

  // Uncomment to print
  // static int count = 1;
  // char buf[ 32 ];
  // sprintf( buf, "graph_%d.dot", count ++ );
  // ofstream out( buf );
  // printAsDotty( out );
  // cerr << "[Dumped " << buf << "]" << endl;

  // Traverse the graph, look for edges of "color" to summarize  
  CNode * c1 = cnodes_store[ conf1->getId( ) ]; 
  CNode * c2 = cnodes_store[ conf2->getId( ) ]; 

  assert( c1 );
  assert( c2 );
  icolor_t conf_color = I_UNDEF;

  // Conflict is due to a negated equality
  if ( conf != NULL )
  {
    const ipartitions_t & p = conf->getIPartitions( );

    if ( isABmixed( p ) )
    {
      colorReset( );
      assert( !colored );
      return egraph.mkFakeInterp( );
    }
    else if ( isAB( p, mask ) )
    {
      // McMillan: set AB as B
      if ( config.proof_set_inter_algo == 0 )
	conf_color = I_B;
      // McMillan: set AB as A
      else if ( config.proof_set_inter_algo == 2 )
	conf_color = I_A;
      // Pudlak: who cares
      else if ( config.proof_set_inter_algo == 1 )
	conf_color = I_A;
    }
    else if ( isAstrict( p, mask ) )
      conf_color = I_A;
    else
    {
      assert( isBstrict( p, mask ) );
      conf_color = I_B;
    }
  }
  // Conflict due to predicates
  else if ( c1->e->isTrue( ) || c2->e->isTrue( ) )
  {
    assert( !c1->e->isTrue ( ) || c2->e->isFalse( ) );
    assert( !c1->e->isFalse( ) || c2->e->isTrue ( ) );
    // There are 3 cases here: the path from true to false
    // is totally in 
    // - A: conf_color is A
    // - B: conf_color is B
    // otherwise there is an ABcommon term in the path,
    // and that is the interpolant
    icolor_t prev_col = I_UNDEF;
    icolor_t path_colors = I_UNDEF;
    vector< CEdge * > sorted_edges;
    CNode * first = c1->next != NULL ? c1 : c2;
    CEdge * curr_edge = first->next;
    while ( curr_edge )
    {
      // Return interpolant if there is a switch
      if ( prev_col == I_A && curr_edge->color == I_B )
      {
	Enode * interpolant = curr_edge->source->e;
	assert( curr_edge->source->color == I_AB );
	// Reset for next call
	colorReset( );
	return egraph.mkEq( egraph.cons( interpolant
	                  , egraph.cons( first->e ) ) );
      }
      // Return interpolant if there is a switch
      if ( prev_col == I_B && curr_edge->color == I_A )
      {
	Enode * interpolant = curr_edge->source->e;
	assert( curr_edge->source->color == I_AB );
	// Reset for next call
	colorReset( );
	return egraph.mkNot( egraph.cons( egraph.mkEq( egraph.cons( interpolant
	                                             , egraph.cons( first->e ) ) ) ) );
      }
      path_colors = static_cast< icolor_t >( path_colors | curr_edge->color );
      prev_col = curr_edge->color;
      curr_edge = curr_edge->target->next;
    }
    assert( path_colors == I_A || path_colors == I_B );
    conf_color = path_colors;
  }
  // Conflict is due to different constants not predicates
  else
  {
    // McMillan: set AB as B
    if ( config.proof_set_inter_algo == 0 )
      conf_color = I_B;
    // McMillan: set AB as A
    else if ( config.proof_set_inter_algo == 2 )
      conf_color = I_A;
    // Pudlak: who cares
    else if ( config.proof_set_inter_algo == 1 )
      conf_color = I_A;
  }

  assert( conf_color == I_A
       || conf_color == I_B );

  Enode * result = NULL;
  path_t pi = path( c1, c2 );
  //
  // Compute interpolant as described in Fuchs et al. paper
  // Ground Interpolation for the Theory of Equality
  //
  // Conflict belongs to A part
  if ( conf_color == I_A )
  {
    list< Enode * > conj;
    // Compute largest subpath of c1 -- c2
    // with B-colorable endpoints
    path_t pi_1, pi_2, theta;
    if ( !getSubpaths( pi, pi_1, theta, pi_2 ) )
    {
      // Compute B( pi_1 ) U B( pi_2 )
      vector< path_t > b_paths;
      B( pi_1, b_paths );
      B( pi_2, b_paths );

      for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
	conj.push_back( I( b_paths[ i ] ) );
      // Finally compute implication
      list< Enode * > conj_impl;
      for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
	conj_impl.push_back( egraph.mkEq( egraph.cons( b_paths[ i ].first->e
		           , egraph.cons( b_paths[ i ].second->e ) ) ) );
      Enode * implicant = egraph.mkAnd( egraph.cons( conj_impl ) );
      Enode * implicated = egraph.mkFalse( );
      conj.push_back( egraph.mkImplies( egraph.cons( implicant
	            , egraph.cons( implicated ) ) ) );
      result = egraph.mkAnd( egraph.cons( conj ) );
    }
    else
    {
      // Compute I( theta )
      conj.push_back( I( theta ) );
      // Compute B( pi_1 ) U B( pi_2 )
      vector< path_t > b_paths;
      B( pi_1, b_paths );
      B( pi_2, b_paths );

      for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
	conj.push_back( I( b_paths[ i ] ) );
      // Finally compute implication
      list< Enode * > conj_impl;
      for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
	conj_impl.push_back( egraph.mkEq( egraph.cons( b_paths[ i ].first->e
		           , egraph.cons( b_paths[ i ].second->e ) ) ) );
      Enode * implicant = egraph.mkAnd( egraph.cons( conj_impl ) );
      Enode * implicated = egraph.mkNot( egraph.cons( egraph.mkEq( egraph.cons( theta.first->e
		                       , egraph.cons( theta.second->e ) ) ) ) );
      conj.push_back( egraph.mkImplies( egraph.cons( implicant
	            , egraph.cons( implicated ) ) ) );
      result = egraph.mkAnd( egraph.cons( conj ) );
    }
  }
  // Much simpler case when conflict belongs to B
  else if ( conf_color == I_B )
  {
    result = I( pi );
  }
  else
  {
    opensmt_error( "something went wrong" );
  }

  assert( result );
  colorReset( );
  assert( !colored );

  // Simplify result by maximizing ands and ors
  result = egraph.maximize( result ); 

  return result;
}

//
// Retrieve subpaths. Returns false if the
// entire path belongs to A, which means
// that the interpolant is "false"
//
bool CGraph::getSubpaths( const path_t & pi
                        , path_t &       pi_1
			, path_t &       theta
			, path_t &       pi_2 )
{
  CNode * x = pi.first;
  CNode * y = pi.second;
  assert( x );
  assert( y );

  // Sorted list of edges from x
  vector< CEdge * > sorted_edges;
  const size_t x_path_length = getSortedEdges( x, y, sorted_edges );
  // Decide maximal B path
  unsigned largest_path_length = 0;

  for ( size_t i = 0 ; i < sorted_edges.size( ) ; ) 
  {
    // Skip A-path
    while ( i < sorted_edges.size( ) 
	 && sorted_edges[ i ]->color == I_A ) i ++;
    if ( i == sorted_edges.size( ) ) continue;
    unsigned path_length = 0;
    // Save source
    CNode * s = i < x_path_length 
	      ? sorted_edges[ i ]->source
	      : sorted_edges[ i ]->target;
    CNode * t = s;
    // Now scan B-path
    while ( i < sorted_edges.size( )
	 && sorted_edges[ i ]->color == I_B )
    { 
      t = i < x_path_length 
	? sorted_edges[ i ]->target 
	: sorted_edges[ i ]->source ;
      i ++;
      path_length ++;
    }
    if ( path_length > largest_path_length )
    {
      assert( s != t );
      largest_path_length = path_length;
      theta.first = s;
      theta.second = t;
    }
    assert( path_length != 0 || s == t );
  }
  // No path found: arbitrary split
  if ( largest_path_length == 0 )
  {
    pi_1.first = pi.first;
    pi_1.second = pi.first;
    pi_2.first = pi.first;
    pi_2.second = pi.second;
    return false;
  }

  // Set pi_1 theta pi_2
  pi_1.first = pi.first;
  pi_1.second = theta.first;
  pi_2.first = theta.second;
  pi_2.second = pi.second; 

  return true;
}

Enode * CGraph::J( const path_t &     p
                 , vector< path_t > & b_paths )
{
  // True on empty path
  if ( p.first == p.second ) return egraph.mkTrue( );

  list< Enode * > conj;
  for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
    conj.push_back( egraph.mkEq( egraph.cons( b_paths[ i ].first->e
	                       , egraph.cons( b_paths[ i ].second->e ) ) ) );
  Enode * implicant = egraph.mkAnd( egraph.cons( conj ) );
  Enode * implicated = egraph.mkEq( egraph.cons( p.first->e, egraph.cons( p.second->e ) ) );

  // Notice that it works also for A-paths like
  //
  // false --> (<= x0 1) --> (<= 2 1)
  //
  // this path says that (<= 2 1) is false, so the implicated
  // should be (not (<= 2 1))
  
  Enode * res = egraph.mkImplies( egraph.cons( implicant, egraph.cons( implicated ) ) );
  return res;
}

Enode * CGraph::I( const path_t & p )
{
  map< path_t, Enode * > cache;
  return Irec( p, cache );
}

Enode * CGraph::Irec( const path_t & p, map< path_t, Enode * > & cache )
{
  // True on empty path
  if ( p.first == p.second ) return egraph.mkTrue( );

  map< path_t, Enode * >::iterator it = cache.find( p );
  // Return previously computed value
  if ( it != cache.end( ) )
    return it->second;

  list< Enode * > conj;
  // Will store factors
  vector< path_t > factors;
  factors.push_back( p );
  // Will store parents of B-path
  vector< path_t > parents;

  const bool a_factor = getFactorsAndParents( p, factors, parents );

  if ( factors.size( ) == 1 )
  {
    // It's an A-path
    if ( a_factor )
    {
      // Compute J
      vector< path_t > b_premise_set;
      B( p, b_premise_set );
      conj.push_back( J( p, b_premise_set ) );

      for ( unsigned i = 0 ; i < b_premise_set.size( ) ; i ++ )
	conj.push_back( Irec( b_premise_set[ i ], cache ) );
    }
    // It's a B-path
    else
    {
      // Recurse on parents
      for ( unsigned i = 0 ; i < parents.size( ) ; i ++ )
	conj.push_back( Irec( parents[ i ], cache ) );
    }
  }
  else
  {
    // Recurse on factors
    for ( unsigned i = 0 ; i < factors.size( ) ; i ++ )
      conj.push_back( Irec( factors[ i ], cache ) );
  }

  Enode * res = egraph.mkAnd( egraph.cons( conj ) );

  assert( res );

  cache[ p ] = res;

  return res;
}

void CGraph::B( const path_t & p
	      , vector< path_t > & b_premise_set )
{
  set< path_t > cache;
  Brec( p, b_premise_set, cache );
}

void CGraph::Brec( const path_t     & p
                 , vector< path_t > & b_premise_set
                 , set< path_t >    & cache )
{
  // Skip trivial call
  if ( p.first == p.second ) return;
  // Skip seen calls
  if ( !cache.insert( p ).second ) return;

  // Will store factors
  vector< path_t > factors;
  factors.push_back( p );
  // Will store parents of B-path
  vector< path_t > parents;

  const bool a_factor = getFactorsAndParents( p, factors, parents );

  if ( factors.size( ) == 1 )
  {
    // It's an A-path
    if ( a_factor )
    {
      for ( unsigned i = 0 ; i < parents.size( ) ; i ++ )
	Brec( parents[ i ], b_premise_set, cache );
    }
    // It's a B-path
    else
      b_premise_set.push_back( p );
  }
  else
  {
    // Recurse on factors
    for ( unsigned i = 0 ; i < factors.size( ) ; i ++ )
      Brec( factors[ i ], b_premise_set, cache );
  }
}
//
// We don't know how to reach x from y. There are
// three cases to consider (see below). This procedure
// retrieves the edges in the correct order to reach
// y from x
//
size_t CGraph::getSortedEdges( CNode * x
                             , CNode * y
			     , vector< CEdge * > & sorted_edges )
{
  assert( x );
  assert( y );
  assert( x != y );

  CNode * x_orig = x;
  CNode * y_orig = y;

  set< CNode * > visited;
  visited.insert( x );
  visited.insert( y );

  vector< CEdge * > & from_x = sorted_edges;
  vector< CEdge * > tmp;

  bool done = false;
  while( !done )
  {
    // Advance x by 1
    if ( x->next != NULL )
    {
      CEdge * candidate = x->next;
      x = x->next->target;
      // Touching an already seen node (by y)
      // x is the nearest common ancestor
      // Clear y vector until x is found
      if ( !visited.insert( x ).second )
      {
	while( !tmp.empty( ) && tmp.back( )->target != x )
	  tmp.pop_back( );	  
	done = true;
      }
      from_x.push_back( candidate );
    }
    if ( done ) break;
    // Advance y by 1
    if ( y->next != NULL )
    {
      CEdge * candidate = y->next;
      y = y->next->target;
      // Touching an already seen node (by x)
      // y is the nearest common ancestor
      // Clear x vector until y is found
      if ( !visited.insert( y ).second )
      {
	while( !from_x.empty( ) && from_x.back( )->target != y )
	  from_x.pop_back( );	  
	done = true;
      }
      tmp.push_back( candidate );
    }
  }
  x = x_orig;
  y = y_orig;

  const size_t x_path_length = sorted_edges.size( );

  // The two paths must collide
  assert( !tmp.empty( ) || sorted_edges.back( )->target == y );
  assert( !sorted_edges.empty( ) || tmp.back( )->target == x );
  assert( sorted_edges.empty( ) 
       || tmp.empty( ) 
       || sorted_edges.back( )->target == tmp.back( )->target );

  // Now load edges from y in the correct order
  while ( !tmp.empty( ) )
  {
    sorted_edges.push_back( tmp.back( ) );
    tmp.pop_back( );
  }

  return x_path_length;
}

//
// Return the set of factors
bool CGraph::getFactorsAndParents( const path_t &     p
				 , vector< path_t > & factors
                                 , vector< path_t > & parents )
{
  assert( factors.size( ) == 1 );
  assert( parents.size( ) == 0 );
  CNode * x = p.first;
  CNode * y = p.second;
  assert( x );
  assert( y );
  vector< CEdge * > sorted_edges;
  const size_t x_path_length = getSortedEdges( x, y, sorted_edges );
  const bool a_factor = sorted_edges[ 0 ]->color == I_A;
  icolor_t last_color = sorted_edges[ 0 ]->color;
  x = 0 < x_path_length 
    ? sorted_edges[ 0 ]->target
    : sorted_edges[ 0 ]->source ;
  y = p.second;
  size_t i = 1;
  // Add parents
  if ( sorted_edges[ 0 ]->reason == NULL )
  {
    CNode * tx = p.first;
    CNode * tn = x;
    assert( tx->e->getArity( ) == tn->e->getArity( ) );
    // Examine children of the congruence edge
    Enode * arg_list_tx, * arg_list_tn;
    for ( arg_list_tx = tx->e->getCdr( )
	, arg_list_tn = tn->e->getCdr( )
	; !arg_list_tx->isEnil( ) 
	; arg_list_tx = arg_list_tx->getCdr( )
	, arg_list_tn = arg_list_tn->getCdr( ) )
    {
      Enode * arg_tx = arg_list_tx->getCar( );
      Enode * arg_tn = arg_list_tn->getCar( );
      if ( arg_tn == arg_tx ) continue;
      // Add parents for further recursion
      parents.push_back( path( cnodes_store[ arg_tx->getId( ) ]
	                     , cnodes_store[ arg_tn->getId( ) ] ) );
    }
  }
  CNode * n;
  while( x != y )
  {
    // Next x
    n = i < x_path_length 
      ? sorted_edges[ i ]->target
      : sorted_edges[ i ]->source ;
    // Retrieve parents for congruence edges
    if ( sorted_edges[ i ]->reason == NULL )
    {
      assert( x->e->getArity( ) == n->e->getArity( ) );
      // Examine children of the congruence edge
      Enode * arg_list_x, * arg_list_n;
      for ( arg_list_x = x->e->getCdr( )
	  , arg_list_n = n->e->getCdr( )
	  ; !arg_list_x->isEnil( ) 
	  ; arg_list_x = arg_list_x->getCdr( )
	  , arg_list_n = arg_list_n->getCdr( ) )
      {
	Enode * arg_x = arg_list_x->getCar( );
	Enode * arg_n = arg_list_n->getCar( );
	if ( arg_n == arg_x ) continue;
	// Add parents for further recursion
        parents.push_back( path( cnodes_store[ arg_x->getId( ) ]
	                       , cnodes_store[ arg_n->getId( ) ] ) );
      }
    }
    // New factor
    if ( i < sorted_edges.size( )
      && sorted_edges[ i ]->color != last_color )
    {
      factors.back( ).second = x;
      factors.push_back( path( x, y ) );
      last_color = sorted_edges[ i ]->color;
    }
    // Increment
    i ++;
    // Pass to next
    x = n;
  }

  return a_factor;
}

void CGraph::printAsDotty( ostream & os )
{
  os << "digraph cgraph {" << endl;
  // Print all nodes
  for ( map< enodeid_t, CNode * >::iterator it = cnodes_store.begin( ) 
      ; it != cnodes_store.end( )
      ; it ++ )
  {
    CNode * c = it->second;
    string color = "grey";
    if ( c->color == I_A ) color = "red";
    if ( c->color == I_B ) color = "blue";
    if ( c->color == I_AB ) color = "green";
    os << c->e->getId( ) 
       << " [label=\"" 
       << c->e 
       << "\",color=\"" << color
       << "\",style=filled]" 
       << endl;
    /*
    if ( c->e->getArity( ) > 0 )
    {
      Enode * args = c->e->getCdr( );
      for ( args = c->e->getCdr( ) 
	  ; !args->isEnil( )
	  ; args = args->getCdr( ) )
      {
	Enode * arg = args->getCar( );
	if ( cnodes_store.find( arg->getId( ) ) == cnodes_store.end( ) )
	  continue;
	os << c->e->getId( ) 
	   << " -> " 
	   << arg->getId( )
	   << " [style=dotted]" 
	   << endl;
      }
    }
    */
  }
  // Print all edges
  for ( size_t i = 0 ; i < cedges.size( ) ; i ++ )
  {
    CEdge * c = cedges[ i ];
    string color = "grey";
    if ( c->color == I_A ) color = "red";
    if ( c->color == I_B ) color = "blue";
    if ( c->color == I_AB ) color = "green";
    os << c->source->e->getId( ) 
       << " -> " 
       << c->target->e->getId( ) 
       << " [color=\"" << color
       << "\",style=\"bold"
       << (c->reason == NULL ? ",dashed" : "")
       << "\"]"
       << endl;
  }
  // Print conflict
  os << conf1->getId( )
     << " -> "
     << conf2->getId( )
     << " [style=bold]"
     << endl;
  os << "}" << endl; 
}

bool CGraph::checkColors( )
{
  for ( vector< CEdge * >::iterator it = cedges.begin( )
      ; it != cedges.end( )
      ; it ++ )
  {
    // Edge that is not involved
    if ( (*it)->color == I_UNDEF )
      continue;
    // Check color is A or B
    if ( (*it)->color != I_A && (*it)->color != I_B )
      return false;
    // Check color is consistent with nodes
    if ( ((*it)->color & (*it)->source->color) == 0 
      || ((*it)->color & (*it)->target->color) == 0 )
    {
      // cerr << "edge col " << (*it)->color << endl;
      // cerr << "   s col " << (*it)->source->color << endl;
      // cerr << "   t col " << (*it)->target->color << endl;
      // cerr << "Edge inconsistent colors: " << (*it) << endl;
      return false;
    }
  }

  return true;
}
#endif
