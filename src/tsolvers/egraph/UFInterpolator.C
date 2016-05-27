/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT2 -- Copyright (C) 2008 - 2012 Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#ifdef PRODUCE_PROOF

#include <sys/wait.h>
#include "UFInterpolator.h"
#include "Egraph.h"

//#define ITP_DEBUG

void CGraph::addCNode( PTRef e )
{
  assert( e != PTRef_Undef );
  map< PTRef, CNode * >::iterator it = cnodes_store.find( e );
  if ( it != cnodes_store.end( ) ) return;
  CNode * n = new CNode( e );
  cnodes_store[ e ] = n;
  cnodes.push_back( n );
  // We need to color this node. It might
  // be a result from some congruence
  // closure operations, hence it might be
  // uncolored
#ifdef ITP_DEBUG
  cerr << "; Adding CNode " << logic.printTerm(e) << endl;
#endif
  if ( logic.getIPartitions(e) == 0 )
  {
#ifdef ITP_DEBUG
    cerr << "; " << logic.printTerm(e) << " has empty partitioning mask" << endl;
#endif
    ipartitions_t max_inner_parts = 0;
    // Set partitions for symbol
    if ( logic.isUF(e) )
      max_inner_parts = logic.getIPartitions(logic.getPterm(e).symb());
      // map Pterm->id to partiions
      // map SymRef to partition
    // Set symbol is shared everywhere
    else
      max_inner_parts = ~max_inner_parts;

    Pterm& p = logic.getPterm(e);
    for(int i = 0; i < p.size(); ++i)
    {
        PTRef arg = p[i];
        assert(logic.getIPartitions(arg) != 0);
        max_inner_parts &= logic.getIPartitions(arg);
    }
    assert( max_inner_parts != 0 );
#ifdef ITP_DEBUG
    cerr << "; " << logic.printTerm(e) << " has now partitioning mask " << max_inner_parts << endl;
#endif
    logic.setIPartitions( e, max_inner_parts );
  }
  assert( logic.getIPartitions(e) != 0 );
}

void CGraph::colorNodes( const ipartitions_t & mask )
{
  for ( size_t i = 0 ; i < cnodes.size( ) ; i ++ )
    colorNodesRec( cnodes[ i ], mask );
}

icolor_t CGraph::colorNodesRec( CNode * c, const ipartitions_t & mask )
{
  assert( logic.getIPartitions(c->e) != 0 );

  // Already done
  if ( colored_nodes.find( c ) != colored_nodes.end( ) )
    return c->color;

  /*
  if ( logic.isUP(c->e) )
  {
    opensmt_error( "Cannot compute interpolants for uninterpreted predicates, sorry" );
    return I_UNDEF;
  }
*/
#ifdef ITP_DEBUG
    cerr << "; Coloring " << logic.printTerm(c->e) << endl;
#endif
    icolor_t color = I_UNDEF;
    Pterm& p = logic.getPterm(c->e);
    if(logic.isUF(c->e) || logic.isUP(c->e))
    {
        if(isAB(logic.getIPartitions(p.symb()), mask))
            color = I_AB;
        else if(isAstrict(logic.getIPartitions(p.symb()), mask))
            color = I_A;
        else
        {
            assert(isBstrict(logic.getIPartitions(p.symb()), mask));
            color = I_B;
        }
#ifdef ITP_DEBUG
        cerr << "; Its symbol has color " << color << endl;
#endif
        for(int i = 0; i < p.size(); ++i)
        {
            PTRef arg = p[i];
            if(cnodes_store.find(arg) != cnodes_store.end())
            {
                colorNodesRec(cnodes_store[arg], mask);
                icolor_t child_color = cnodes_store[arg]->color;
                if(color == I_AB)
                {
                    if(child_color == I_A) color = I_A;
                    else if(child_color == I_B) color = I_B;
                }
                else if(color == I_A)
                {
                    if(child_color == I_B) opensmt_error("Term I_A has child I_B");
                }
                else if(color == I_B)
                {
                    if(child_color == I_A) opensmt_error("Term I_B has child I_A");
                }
#ifdef ITP_DEBUG
                cerr << "; Now the term has color " << color << endl;
#endif
            }
        }
    }
    else
    {
        if(isAB(logic.getIPartitions(c->e), mask))
            color = I_AB;
        else if(isAstrict(logic.getIPartitions(c->e), mask))
            color = I_A;
        else
        {
            assert(isBstrict(logic.getIPartitions(c->e), mask));
            color = I_B;
        }
#ifdef ITP_DEBUG
        cerr << "; Variable, color " << color << endl;
#endif
    }
    colored_nodes.insert(c);
    return c->color = color;

/*
  if ( logic.isUP(c->e) )
  {
    opensmt_error( "Cannot compute interpolants for uninterpreted predicates, sorry" );
    // Predicate symbol: color depending on the arguments
    // Decide color of term as intersection
    color = I_AB;
    assert( logic.getIPartitions(logic.getPterm(c->e).symb()) != 0 );

    if ( isAstrict( logic.getIPartitions(logic.getPterm(c->e).symb()), mask ) )
      color = I_A;
    else if ( isBstrict( logic.getIPartitions(logic.getPterm(c->e).symb()), mask ) )
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
  else if ( isAB( logic.getIPartitions(c->e), mask ) )
  {
    color = I_AB;
  }
  else if ( isAstrict( logic.getIPartitions(c->e), mask ) )
  {
    color = I_A;
  }
  else
  {
    assert( isBstrict( logic.getIPartitions(c->e), mask ) );
    color = I_B;
  }

  c->color = color;

  Pterm& p = logic.getPterm(c->e);
  for(int i = 0; i < p.size(); ++i)
  {
      PTRef arg = p[i];
    // Not necessairily an argument is needed in the graph
    if ( cnodes_store.find( arg ) != cnodes_store.end( ) )
      colorNodesRec( cnodes_store[ arg ], mask );
  }

  assert( c->color == I_A 
       || c->color == I_B 
       || c->color == I_AB );

  assert( colored_nodes.find( c ) == colored_nodes.end( ) );
  colored_nodes.insert( c );

  return c->color;
  */
}

void CGraph::addCEdge( PTRef s, PTRef t, PTRef r )
{
  assert( s != PTRef_Undef);
  assert( t != PTRef_Undef);
  // Retrieve corresponding nodes
  CNode * cs = cnodes_store[ s ];
  CNode * ct = cnodes_store[ t ];
  // Create edge
  CEdge * edge = new CEdge( cs, ct, r );
  // Storing edge in cs and ct
  assert( cs->next == NULL ); 
  cs->next = edge;
  cedges.push_back( edge ); 
/*
  static int ccong = 0;
  if(r == PTRef_Undef) //congruence edge
  {
      if(ccong == 1)
          L[path(cs, ct)] = I_A;
      else
          L[path(cs, ct)] = I_B;
      cerr << "; Coloring congruence edge " << logic.printTerm(s) << " -> " << logic.printTerm(t) << " with " << L[path(cs, ct)] << endl;
      ++ccong;
  }
*/
}

void CGraph::color( const ipartitions_t & mask )
{
  assert( conf1 != PTRef_Undef);
  assert( conf2 != PTRef_Undef);
  // Starting from
  CNode * c1 = cnodes_store[ conf1 ]; 
  CNode * c2 = cnodes_store[ conf2 ]; 
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
      if ( x->next->reason == PTRef_Undef
	&& cache_edges.insert( x->next ).second )
      {
	    CNode * n = x->next->target;
    	assert( logic.getPterm(x->e).size() == logic.getPterm(n->e).size() );
        // getArity = pterm->size
        Pterm& px = logic.getPterm(x->e);
        Pterm& pn = logic.getPterm(n->e);
    	// Iterate over function's arguments
        for(int i = 0; i < px.size(); ++i)
    	{
            PTRef arg_x = px[i];
            PTRef arg_n = pn[i];

	        if ( arg_x == arg_n ) continue;

    	    CNode * arg_n1 = cnodes_store[ arg_x ];
	        CNode * arg_n2 = cnodes_store[ arg_n ];
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
      if ( x->next->reason == PTRef_Undef
    	&& cache_edges.insert( x->next ).second )
      {
	    CNode * n = x->next->target;
    	assert( logic.getPterm(x->e).size() == logic.getPterm(n->e).size() );
        Pterm& px = logic.getPterm(x->e);
        Pterm& pn = logic.getPterm(n->e);
    	// Iterate over function's arguments
        for(int i = 0; i < px.size(); ++i)
    	{
            PTRef arg_x = px[i];
            PTRef arg_n = pn[i];

             if ( arg_x == arg_n ) continue;

    	  CNode * arg_n1 = cnodes_store[ arg_x ];
	      CNode * arg_n2 = cnodes_store[ arg_n ];
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
    if ( x->next->reason == PTRef_Undef )
    {
      assert( logic.getPterm(x->e).size() == logic.getPterm(n->e).size() );
#if ITERATIVE_COLORING
#else
      // Color children of the congruence relation, and
      // introduce intermediate nodes if necessary
      Pterm& px = logic.getPterm(x->e);
      Pterm& pn = logic.getPterm(n->e);
      for(int i = 0; i < pn.size(); ++i)
      {
          PTRef arg_x = px[i];
          PTRef arg_n = pn[i];
	    if ( arg_x == arg_n ) continue;

    	// Check that path has not been considered yet
	    if ( !path_seen.insert( make_pair( arg_x, arg_n ) ).second )
    	  continue;

	    // Call recursively on arguments
    	colorEdgesRec( cnodes_store[ arg_x ]
	                 , cnodes_store[ arg_n ] 
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
        vec<PTRef> new_args;
        Pterm& px = logic.getPterm(x->e);
        Pterm& pn = logic.getPterm(n->e);
        for(int i = 0; i < pn.size(); ++i)
	    {
            PTRef arg_x = px[i];
            PTRef arg_n = pn[i];

    	  // If same node, keep
	      if ( arg_x == arg_n )
    	  {
	        new_args.push( arg_x );
    	  } 
	      else
    	  {
	        assert( cnodes_store.find( arg_x ) != cnodes_store.end( ) );
	        assert( cnodes_store.find( arg_n ) != cnodes_store.end( ) );
    	    CNode * cn_arg_x = cnodes_store[ arg_x ];
	        CNode * cn_arg_n = cnodes_store[ arg_n ];
	        // There is either a path from arg_x to ABcommon
    	    // or a path from arg_n to ABcommon (or both)
    	    assert( cn_arg_x->next != NULL
	    	 || cn_arg_n->next != NULL );

    	    // If argument of x is incompatible with n
	        if ( ((cn_arg_x->color & n->color) == 0) )
	        {
    	      // Browse the eq-class of cn_arg_x and find an ABcommon symbol
              PTRef v = arg_x;
              PTRef abcommon = PTRef_Undef;
              while( abcommon == PTRef_Undef)
              {
                  const Enode& en_v = egraph.getEnode(v);
                  PTRef cand = egraph.ERefToTerm(en_v.getNext());
                  if ( isAB( logic.getIPartitions(cand), mask ) ) abcommon = cand;
                  v = cand;
    	      }
	          assert( abcommon != PTRef_Undef );
	          assert( cnodes_store.find( abcommon ) != cnodes_store.end( ) );
    	      CNode * new_arg_x = cnodes_store[ abcommon ];
	          assert( new_arg_x->color == I_AB );
	          new_args.push( abcommon );
	        }
    	    // If argument of n is incompatible with x
	        else if ( ((cn_arg_n->color & x->color) == 0) )
	        {
    	      // Browse the eq-class of cn_arg_x and find an ABcommon symbol
              PTRef v = arg_n;
              PTRef abcommon = PTRef_Undef;
              while( abcommon == PTRef_Undef )
              {
                  const Enode& en_v = egraph.getEnode(v);
                  PTRef cand = egraph.ERefToTerm(en_v.getNext());
                  if ( isAB( logic.getIPartitions(cand), mask ) ) abcommon = cand;
                  v = cand;
	          }
    	      assert( abcommon != PTRef_Undef );
	          assert( cnodes_store.find( abcommon ) != cnodes_store.end( ) );
	          CNode * new_arg_n = cnodes_store[ abcommon ];
    	      assert( new_arg_n->color == I_AB );
	          new_args.push( abcommon );
	        }
	        else
    	    {
	          opensmt_error( "something went wrong" );
	        }
	    // New arguments must be shared
        assert(new_args.size() > 0);
	    assert( cnodes_store[ new_args[0] ]->color == I_AB );
	  }
	}

    char **msg;
    PTRef nn = logic.mkFun(logic.getPterm(x->e).symb(), new_args, msg);
    /*
    if(isAstrict(logic.getIPartitions(new_args[0]), mask) && isBstrict(logic.getIPartitions(new_args[1]), mask))
        logic.addIPartitions(nn, 0);
    else if(isBstrict(logic.getIPartitions(new_args[0]), mask) && isAstrict(logic.getIPartitions(new_args[1]), mask))
        logic.addIPartitions(nn, 0);
        */

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
	addCEdge( x->e, nn, PTRef_Undef );
	assert( x->next->target == cnn );
	// Choose a color
	assert( x->color == I_A 
	    || x->color == I_B 
	    || x->color == I_AB );

	if ( x->color == I_AB )
	{
        cedges.back( )->color = (rand() % 2) ? I_A : I_B;
//        cerr << "; Coloring edge " << logic.printTerm(cedges.back()->source->e) << " -> " << logic.printTerm(cedges.back()->target->e) << " with color " << cedges.back()->color << endl;
        /*
            // McMillan: set AB as B
            if ( usingStrong())
                cedges.back( )->color = I_B;
            // McMillan': set AB as A
            else if ( usingWeak())
                cedges.back( )->color = I_A;
            // Random
            else if ( usingRandom() )
                cedges.back( )->color = (rand() % 2) ? I_A : I_B;
        */
	}
	else
	  cedges.back( )->color = x->color;

	addCEdge( nn, n->e, PTRef_Undef );	
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
	    x->next->color = (rand() % 2) ? I_A : I_B;
//        cerr << "; Coloring edge " << logic.printTerm(x->next->source->e) << " -> " << logic.printTerm(x->next->target->e) << " with color " << x->next->color << endl;
        /*
	  // McMillan: set AB as B
	  if ( usingStrong()  )
	    x->next->color = I_B;
	  // McMillan: set AB as A
	  else if ( usingWeak() )
	    x->next->color = I_A;
	  // Random
	  else if ( usingRandom() )
	    x->next->color = (rand() % 2) ? I_A : I_B;
        */
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

      const ipartitions_t & p = logic.getIPartitions(x->next->reason);
      //cerr << "; Partition = " << p << endl;
      //cerr << "; Mask = " << mask << endl;
      if ( isABmixed( p ) )
	    return false;
      else if ( isAstrict( p, mask ) )
      {
	    x->next->color = I_A;
       //   cerr << ";IsAstrict" << endl;
        A_basic.push(x->next->reason);
      }
      else if ( isBstrict( p, mask ) )
      {
         // cerr << ";IsBstrict" << endl;
        B_basic.push(x->next->reason);
    	x->next->color = I_B;
      }
      else 
      {
         // cerr << ";IsAB" << endl;
          A_basic.push(x->next->reason);
          //B_basic.push(x->next->reason);
	assert( isAB( p, mask ) );
	  x->next->color = (rand() % 2) ? I_A : I_B;
//        cerr << "; Coloring edge " << logic.printTerm(x->next->source->e) << " -> " << logic.printTerm(x->next->target->e) << " with color " << x->next->color << endl;
      /*
	// McMillan: set AB as B
	if ( usingStrong()  )
	  x->next->color = I_B;
	// McMillan: set AB as A
	else if ( usingWeak() )
	  x->next->color = I_A;
	// Random
	else if ( usingRandom() )
	  x->next->color = (rand() % 2) ? I_A : I_B;
      */
      }

/*
      cerr << ";Coloring edge: " << logic.printTerm(x->next->reason) << endl;
       cerr << ";        parts: " << logic.getIPartitions(x->next->reason) << endl;
       cerr << ";         mask: " << mask << endl;
       cerr << ";        color: " << x->next->color << endl;
*/
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

PTRef
CGraph::interpolate_flat(const path_t& p)
{
    flat = true;

    cerr << "; Interpolating flat path (" << logic.printTerm(p.first->e) << "," << logic.printTerm(p.second->e) << ")" << endl;
    vec<PTRef> args;
    bool la, lb, lab, ra, rb, rab;

    vector<path_t> factors;
    factors.push_back(p);
    vector<path_t> parents;
    const bool a_factor = getFactorsAndParents( p, factors, parents );
    // this should be a flat path
    assert(parents.size() == 0);

    //cerr << "; Flat path has " << factors.size() << " factors:" << endl;
    //for(int i = 0; i < factors.size(); ++i) cerr << "; Factor " << i << " = (" << logic.printTerm(factors[i].first->e) << "," << logic.printTerm(factors[i].second->e) << ")" << endl;

    for(int i = 0; i < factors.size(); i += 3)
    {
        int j = i + 2;
        if(j >= factors.size()) j = (factors.size() - 1);

        path_t pf(factors[i].first, factors[j].second);
        cerr << "; Subpath (" << logic.printTerm(pf.first->e) << "," << logic.printTerm(pf.second->e) << ")" << endl;

        CNode *l = pf.first;
        CNode *r = pf.second;
        la = lb = lab = ra = rb = rab = false;
        if(l->color == I_A) la = true;
        else if(l->color == I_B) lb = true;
        else lab = true;
        if(r->color == I_A) ra = true;
        else if(r->color == I_B) rb = true;
        else rab = true;

        assert(!((la && rb) || (lb && ra)));
        bool b = rand() % 2;
        if(la || ra) // conflict in A, call I' or not S
        {
            assert(i == 0);
            if(b)
            {
                cerr << "; Calling I'" << endl;
                args.push(Iprime(pf));
            }
            else
            {
                cerr << "; Calling S" << endl;
                args.push(logic.mkNot(ISwap(pf)));
            }
        }
        else if(lb || rb) // conflict in B, call I or not S'
        {
            assert(j == (factors.size() - 1));
            if(b)
            {
                cerr << "; Calling I" << endl;
                args.push(I(pf));
            }
            else
            {
                cerr << "; Calling S'" << endl;
                args.push(logic.mkNot(IprimeSwap(pf)));
            }
        }
        else // conflict has global endpoints
        {
            if(b)
            {
                cerr << "; Calling I" << endl;
                args.push(I(pf));
            }
            else
            {
                cerr << "; Calling S'" << endl;
                args.push(logic.mkNot(IprimeSwap(pf)));
            }
        }
    }
    PTRef itp = logic.mkAnd(args);
    assert(itp != PTRef_Undef);
    cerr << "; Flat itp: " << logic.printTerm(itp) << endl;
    flat = false;
    return itp;
}


//
// Here mask is a bit-mask of the form 1..10..0
// which indicates the current splitting for the
// formula into A and B.
//
PTRef
CGraph::getInterpolant( const ipartitions_t & mask )
{
    cerr << "; Interpolating QF_UF using ";
    if(usingStrong())
        cerr << "Strong";
    else if(usingWeak())
	cerr << "Weak";
    else if(usingRandom())
	cerr << "Random";
    else
        opensmt_error("This EUF interpolation algorithm does not exist");
    cerr << endl;

  assert( !colored );

  srand(2);
/*
    cerr << ";\n;\n;\n;\n;CGraph edges: " << endl;
    vec<PTRef> ced;
    for(int i = 0; i < cedges.size(); ++i)
    {
        vec<PTRef> lala;
        lala.push(cedges[i]->source->e);
        lala.push(cedges[i]->target->e);
        ced.push(logic.mkEq(lala));
    }
    PTRef cand = logic.mkAnd(ced);
    cerr << ';' << logic.printTerm(cand) << endl;
*/


  color( mask );

  if ( !colored )
  {
    //colorReset( );
    assert( !colored );
    return interpolant = logic.getTerm_true();
    //return egraph.mkFakeInterp( );
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
  CNode * c1 = cnodes_store[ conf1 ]; 
  CNode * c2 = cnodes_store[ conf2 ]; 

  assert( c1 );
  assert( c2 );
  conf_color = I_UNDEF;

  // Conflict is due to a negated equality
  if ( conf != PTRef_Undef )
  {
    const ipartitions_t & p = logic.getIPartitions(conf);

    //cerr << ";P = " << p << ", MASK = " << mask << endl;
    if ( isABmixed( p ) )
    {
      //colorReset( );
      //assert( !colored );
      return interpolant = logic.getTerm_true();
      //return egraph.mkFakeInterp( );
    }
    else if ( isAB( p, mask ) )
    {
   //     cerr << "; CONFLICT IS AB" << endl;
        conf_color = (rand() % 2) ? I_A : I_B;
     //   cerr << "; Chose random side " << conf_color << endl;
        /*
        // McMillan: set AB as B
        if ( usingStrong() )
            conf_color = I_B;
        // McMillan: set AB as A
        else if ( usingWeak() )
            conf_color = I_A;
        // Random
        else if ( usingRandom())
            conf_color = (rand() % 2) ? I_A : I_B;
        */
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
  else if ( logic.isTrue(c1->e) || logic.isTrue(c2->e) )
  {
    assert( !logic.isTrue(c1->e) || logic.isFalse(c2->e) );
    assert( !logic.isFalse(c1->e) || logic.isTrue(c2->e) );
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
    	PTRef interpolant = curr_edge->source->e;
	    assert( curr_edge->source->color == I_AB );
    	// Reset for next call
	    //colorReset( );
	//cerr << logic.printTerm(interpolant) << " =1 " << logic.printTerm(first->e) << endl;
	conf_color = I_B; //actually AB TODO
	break;
        return interpolant = logic.mkEq(interpolant, first->e);
    	//return egraph.mkEq( egraph.cons( interpolant
	      //            , egraph.cons( first->e ) ) );
      }
      // Return interpolant if there is a switch
      if ( prev_col == I_B && curr_edge->color == I_A )
      {
    	PTRef interpolant = curr_edge->source->e;
    	assert( curr_edge->source->color == I_AB );
	    // Reset for next call
    	//colorReset( );
	//cerr << logic.printTerm(interpolant) << " =2 " << logic.printTerm(first->e) << endl;
	conf_color = I_B; //actually AB TODO
	break;
        return interpolant = logic.mkNot( logic.mkEq(interpolant, first->e) );
	    //return egraph.mkNot( egraph.cons( egraph.mkEq( egraph.cons( interpolant
	      //                                       , egraph.cons( first->e ) ) ) ) );
      }
      path_colors = static_cast< icolor_t >( path_colors | curr_edge->color );
      prev_col = curr_edge->color;
      curr_edge = curr_edge->target->next;
    }
    if(conf_color == I_UNDEF)
    {
        assert( path_colors == I_A || path_colors == I_B );
        conf_color = path_colors;
    }
  }
  // Conflict is due to different constants not predicates
  else
  {
    // McMillan: set AB as B
    if ( usingStrong() )
      conf_color = I_B;
    // McMillan: set AB as A
    else if ( usingWeak() )
      conf_color = I_A;
    // Random
    else if ( usingRandom() )
      conf_color = (rand() % 2) ? I_A : I_B;
  }

  assert( conf_color == I_A
       || conf_color == I_B );

  PTRef result = PTRef_Undef;
  path_t pi = path( c1, c2 );
  //
  // Compute interpolant as described in Fuchs et al. paper
  // Ground Interpolation for the Theory of Equality
  //
  // Conflict belongs to A part
  if ( conf_color == I_A )
  {
//      cerr << "; Conflict in A" << endl;
    if(usingStrong())
        result = Iprime( pi );
    else if(usingWeak())
        result = logic.mkNot(ISwap(pi));
    else if(usingRandom())
        result = (rand() % 2) ? Iprime(pi) : logic.mkNot(ISwap(pi));
  }
  // Much simpler case when conflict belongs to B
  else if ( conf_color == I_B )
  {
  //    cerr << "; Conflict in B" << endl;
    if(usingStrong())
        result = I( pi );
    else if(usingWeak())
        result = logic.mkNot(IprimeSwap(pi));
    else if(usingRandom())
        result = (rand() % 2) ? I(pi) : logic.mkNot(IprimeSwap(pi));
  }
  else
  {
    opensmt_error( "something went wrong" );
  }

  assert( result != PTRef_Undef );
  //colorReset( );
  //assert( !colored );

  // Simplify result by maximizing ands and ors
  //result = egraph.maximize( result ); 

  //cerr << "; Size stats:\n; Max height: " << max_height << "\n; Max width: " << max_width << endl;

  interpolant = result;
  verifyInterpolantWithExternalTool(mask);
  return interpolant;
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
//    cerr << "; Computing subpaths" << endl;
  // Sorted list of edges from x
  vector< CEdge * > sorted_edges;
  const size_t x_path_length = getSortedEdges( x, y, sorted_edges );

    CNode *lnode = NULL;
    CNode *rnode = NULL;

    icolor_t scolor = x->color;
    icolor_t tcolor = y->color;
    if(scolor == I_B || scolor == I_AB) lnode = x;
    else if(tcolor == I_B || tcolor == I_AB) lnode = y;
    if(tcolor == I_B || tcolor == I_AB) rnode = y;
    else if(scolor == I_B || scolor == I_AB) rnode = x;

    bool rfound = false;
    if(rnode != NULL) rfound = true;

    if(lnode == NULL || rnode == NULL)
    {
    for(int i = 0; i < sorted_edges.size(); ++i)
    {
        scolor = sorted_edges[i]->source->color;
        tcolor = sorted_edges[i]->target->color;
//        cerr << "; (" << logic.printTerm(sorted_edges[i]->source->e) << " has color " << scolor << endl;
//        cerr << "; (" << logic.printTerm(sorted_edges[i]->target->e) << " has color " << tcolor << endl;
        if(lnode == NULL)
        {
            if(scolor == I_B || scolor == I_AB) lnode = sorted_edges[i]->source;
            else if(tcolor == I_B || tcolor == I_AB) lnode = sorted_edges[i]->target;
        }
        if(!rfound)
        {
            if(tcolor == I_B || tcolor == I_AB) rnode = sorted_edges[i]->target;
            else if(scolor == I_B || scolor == I_AB) rnode = sorted_edges[i]->source;
        }

//        if(lnode != NULL) cerr << "; LNODE " << logic.printTerm(lnode->e) << endl;
//        if(rnode != NULL) cerr << "; RNODE " << logic.printTerm(rnode->e) << endl;
    }
    }

    if(lnode == NULL || rnode == NULL || lnode == rnode)
    {
        //theta empty
        pi_1.first = pi.first;
        pi_1.second = pi.first;
        pi_2.first = pi.first;
        pi_2.second = pi.second;
        return false;
    }

    theta.first = lnode;
    theta.second = rnode;
    pi_1.first = pi.first;
    pi_1.second = theta.first;
    pi_2.first = theta.second;
    pi_2.second = pi.second;
    return true;


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

bool
CGraph::getSubpathsSwap( const path_t & pi
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

    CNode *lnode = NULL;
    CNode *rnode = NULL;

    icolor_t scolor = x->color;
    icolor_t tcolor = y->color;
    if(scolor == I_A || scolor == I_AB) lnode = x;
    else if(tcolor == I_A || tcolor == I_AB) lnode = y;
    if(tcolor == I_A || tcolor == I_AB) rnode = y;
    else if(scolor == I_A || scolor == I_AB) rnode = x;

    bool rfound = false;
    if(rnode != NULL) rfound = true;

    if(lnode == NULL || rnode == NULL)
    {
    for(int i = 0; i < sorted_edges.size(); ++i)
    {
        scolor = sorted_edges[i]->source->color;
        tcolor = sorted_edges[i]->target->color;
        if(lnode == NULL)
        {
            if(scolor == I_A || scolor == I_AB) lnode = sorted_edges[i]->source;
            else if(tcolor == I_A || tcolor == I_AB) lnode = sorted_edges[i]->target;
        }
        if(!rfound)
        {
            if(tcolor == I_A || tcolor == I_AB) rnode = sorted_edges[i]->target;
            else if(scolor == I_A || scolor == I_AB) rnode = sorted_edges[i]->source;
        }
    }
    }

    if(lnode == NULL || rnode == NULL || lnode == rnode)
    {
        //theta empty
        pi_1.first = pi.first;
        pi_1.second = pi.first;
        pi_2.first = pi.first;
        pi_2.second = pi.second;
        return false;
    }

    theta.first = lnode;
    theta.second = rnode;
    pi_1.first = pi.first;
    pi_1.second = theta.first;
    pi_2.first = theta.second;
    pi_2.second = pi.second;
    return true;



  // Decide maximal A path
  unsigned largest_path_length = 0;

  for ( size_t i = 0 ; i < sorted_edges.size( ) ; ) 
  {
    // Skip B-path
    while ( i < sorted_edges.size( ) 
	 && sorted_edges[ i ]->color == I_B ) i++;
    if ( i == sorted_edges.size( ) ) continue;
    unsigned path_length = 0;
    // Save source
    CNode * s = i < x_path_length 
	      ? sorted_edges[ i ]->source
	      : sorted_edges[ i ]->target;
    CNode * t = s;
    // Now scan A-path
    while ( i < sorted_edges.size( )
	 && sorted_edges[ i ]->color == I_A )
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

PTRef
CGraph::J( const path_t &     p
                 , vector< path_t > & b_paths )
{
  // True on empty path
  if ( p.first == p.second ) return logic.getTerm_true();

  vec< PTRef > conj;
  for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
  {
    conj.push(logic.mkEq(b_paths[i].first->e, b_paths[i].second->e));
  //  conj.push_back( egraph.mkEq( egraph.cons( b_paths[ i ].first->e
	//                       , egraph.cons( b_paths[ i ].second->e ) ) ) );
  }
  PTRef implicant = logic.mkAnd(conj);
  //PTRef implicant = egraph.mkAnd( egraph.cons( conj ) );
  PTRef implicated = logic.mkEq(p.first->e, p.second->e);
  //PTRef implicated = egraph.mkEq( egraph.cons( p.first->e, egraph.cons( p.second->e ) ) );

  // Notice that it works also for A-paths like
  //
  // false --> (<= x0 1) --> (<= 2 1)
  //
  // this path says that (<= 2 1) is false, so the implicated
  // should be (not (<= 2 1))
  
  PTRef res = logic.mkImpl(implicant, implicated);
  //PTRef res = egraph.mkImplies( egraph.cons( implicant, egraph.cons( implicated ) ) );
  return res;
}

PTRef
CGraph::Iprime( const path_t& pi )
{
#ifdef ITP_DEBUG
  cerr << ";Computing Iprime(" << logic.printTerm(pi.first->e) << "," << logic.printTerm(pi.second->e) << ")" << endl;
#endif
    vec<PTRef> conj;
    // Compute largest subpath of c1 -- c2
    // with B-colorable endpoints
    path_t pi_1, pi_2, theta;
    bool empty_theta = !getSubpaths( pi, pi_1, theta, pi_2 );
    // Compute B( pi_1 ) U B( pi_2 )
    vector< path_t > b_paths;
    B( pi_1, b_paths );
    B( pi_2, b_paths );

    if(!empty_theta)
    {
#ifdef ITP_DEBUG
        cerr << ";Theta: (" << logic.printTerm(theta.first->e) << "," << logic.printTerm(theta.second->e) << ")" << endl;
#endif
        conj.push(I(theta));
    }
#ifdef ITP_DEBUG
    cerr << ";B of pi1 UNION pi2 has size " << b_paths.size() << endl;
#endif
    for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
        conj.push( I( b_paths[ i ] ) );
    // Finally compute implication
    vec< PTRef > conj_impl;
    for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
    {
      conj_impl.push( logic.mkEq( b_paths[i].first->e, b_paths[i].second->e) );
    }
    PTRef implicant = logic.mkAnd(conj_impl);
    PTRef implicated = PTRef_Undef;
    if(empty_theta)
        implicated = logic.getTerm_false();
    else
        implicated = logic.mkNot( logic.mkEq (theta.first->e, theta.second->e ) );
    conj.push( logic.mkImpl(implicant, implicated) );
    return logic.mkAnd(conj);
}

PTRef
CGraph::IprimeSwap( const path_t& pi )
{
#ifdef ITP_DEBUG
  cerr << ";Computing IprimeSwap(" << logic.printTerm(pi.first->e) << "," << logic.printTerm(pi.second->e) << ")" << endl;
#endif
    vec<PTRef> conj;
    // Compute largest subpath of c1 -- c2
    // with B-colorable endpoints
    path_t pi_1, pi_2, theta;
    bool empty_theta = !getSubpathsSwap( pi, pi_1, theta, pi_2 );
    // Compute B( pi_1 ) U B( pi_2 )
    vector< path_t > b_paths;
    BSwap( pi_1, b_paths );
    BSwap( pi_2, b_paths );

    if(!empty_theta)
    {
#ifdef ITP_DEBUG
        cerr << ";Theta: (" << logic.printTerm(theta.first->e) << "," << logic.printTerm(theta.second->e) << ")" << endl;
#endif
        conj.push(ISwap(theta));
    }
#ifdef ITP_DEBUG
    cerr << ";BSwap of pi1 UNION pi2 has size " << b_paths.size() << endl;
#endif


    for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
        conj.push( ISwap( b_paths[ i ] ) );
    // Finally compute implication
    vec< PTRef > conj_impl;
    for ( unsigned i = 0 ; i < b_paths.size( ) ; i ++ )
    {
      conj_impl.push( logic.mkEq( b_paths[i].first->e, b_paths[i].second->e) );
    }
    PTRef implicant = logic.mkAnd(conj_impl);
    PTRef implicated = PTRef_Undef;
    if(empty_theta)
        implicated = logic.getTerm_false();
    else
        implicated = logic.mkNot( logic.mkEq (theta.first->e, theta.second->e ) );
    conj.push( logic.mkImpl(implicant, implicated) );
    return logic.mkAnd(conj);
}

PTRef
CGraph::I( const path_t & p )
{
  map< path_t, PTRef > cache;
  return Irec( p, cache , 1);
}

PTRef
CGraph::ISwap( const path_t & p )
{
  map< path_t, PTRef > cache;
  return IrecSwap( p, cache , 1);
}

PTRef
CGraph::Irec( const path_t & p, map< path_t, PTRef > & cache , unsigned int h)
{
    if(h > max_height) max_height = h;
  // True on empty path
  if ( p.first == p.second ) return logic.getTerm_true();

    string lstr(";");
    for(int i = 0; i < h; ++i) lstr += ' ';

/*
  map< path_t, PTRef >::iterator it = cache.find( p );
  // Return previously computed value
  if ( it != cache.end( ) )
    return it->second;
*/

#ifdef ITP_DEBUG
  cerr << lstr << "Computing Irec(" << logic.printTerm(p.first->e) << "," << logic.printTerm(p.second->e) << ")" << endl;
#endif
  vec< PTRef > conj;
  vec< PTRef > conj_swap;
  // Will store factors
  vector< path_t > factors;
  factors.push_back( p );
  // Will store parents of B-path
  vector< path_t > parents;

  const bool a_factor = getFactorsAndParents( p, factors, parents );

  //if(!flat && parents.size() == 0) return interpolate_flat(p);

  if ( factors.size( ) == 1 )
  {
#ifdef ITP_DEBUG
    cerr << lstr << "Factor has size 1" << endl;
#endif
    // It's an A-path
    if ( a_factor )
    {
#ifdef ITP_DEBUG
      cerr << lstr << "Single factor is an A-factor" << endl;
#endif
      // Compute J
      vector< path_t > b_premise_set;
      B( p, b_premise_set );
      conj.push( J( p, b_premise_set ) );
#ifdef ITP_DEBUG
        cerr << lstr << "B-set has size " << b_premise_set.size() << endl;
#endif
        for ( unsigned i = 0 ; i < b_premise_set.size( ) ; i ++ )
        {
            path_t& fac = b_premise_set[i];
            assert(L.find(fac) != L.end());
#ifdef ITP_DEBUG
            cerr << "; Checking label of path (" << logic.printTerm(fac.first->e) << ", " << logic.printTerm(fac.second->e) << ") = " << L[fac] << endl;
#endif
            if(L[fac] == I_B)
            {
#ifdef ITP_DEBUG
                cerr << "; Not swapping" << endl;
#endif
                conj.push( Irec( b_premise_set[ i ], cache, h + 1 ) );
            }
            else
            {
                //swap here
                conj_swap.push(logic.mkNot(IprimeSwap(fac)));
#ifdef ITP_DEBUG
                cerr << "; Swapping from I to (not S')" << endl;
#endif
            }
        }
        if(conj_swap.size() > 0)
        {
            /*
            PTRef implicant = logic.mkNot(logic.mkEq(p.first->e, p.second->e));
            PTRef implicated = logic.mkAnd(conj_swap);
            conj.push(logic.mkImpl(implicant, implicated));
            */
            conj.push(logic.mkAnd(conj_swap));
        }
    }
    // It's a B-path
    else
    {
//        cerr << lstr << "Single factor is a B-factor" << endl;
      // Recurse on parents
      for ( unsigned i = 0 ; i < parents.size( ) ; i ++ )
         conj.push( Irec( parents[i], cache, h + 1 ) );
    }
  }
  else
  {
    //cerr << lstr << "Multiple factors for path (" << logic.printTerm(p.first->e) << "," << logic.printTerm(p.second->e) << ")" << endl;
    //  divided = true;
    // Recurse on factors
    //if(!divided)
    if(factors.size() > 3 && config.itp_euf_alg() > 3)
    {
#ifdef ITP_DEBUG
    cerr << lstr << "Multiple factors for path (" << logic.printTerm(p.first->e) << "," << logic.printTerm(p.second->e) << ")" << endl;
    cerr << "Factors" << endl;
    for(int i = 0; i < factors.size(); ++i)
        cerr << " | " << logic.printTerm(factors[i].first->e) << '-' << logic.printTerm(factors[i].second->e) << endl;
#endif
    bool la, lb, lab, ra, rb, rab;
    divided = true;

    for(int i = 0; i < factors.size(); i += 3)
    {
        int j = i + 2;
        if(j >= factors.size()) j = (factors.size() - 1);

        path_t pf(factors[i].first, factors[j].second);
#ifdef ITP_DEBUG
        cerr << "; Subpath (" << logic.printTerm(pf.first->e) << "," << logic.printTerm(pf.second->e) << ")" << endl;
#endif
        CNode *l = pf.first;
        CNode *r = pf.second;

        vector<path_t> infactors;
        infactors.push_back(pf);
        vector<path_t> inparents;
        const bool a_factor = getFactorsAndParents(pf, infactors, inparents);
        if(j < (factors.size() - 1))
            assert(infactors.size() >= 3);
        if(infactors.size() >= 2)
        {
#ifdef ITP_DEBUG
            cerr << "At least 2 factors" << endl;
#endif
            if(a_factor)
            {
#ifdef ITP_DEBUG
                cerr << "A factors, calling S'" << endl;
#endif
                conj.push(logic.mkNot(IprimeSwap(pf)));
            }
            else
            {
#ifdef ITP_DEBUG
                cerr << "B factors, calling I" << endl;
#endif
                conj.push(Irec(pf, cache, h + 1));
            }
            continue;
        }
#ifdef ITP_DEBUG
        cerr << "Only 1 factor" << endl;
#endif


/*
        vector< CEdge * > sorted_edges;
        const size_t x_path_length = getSortedEdges(l, r, sorted_edges);

        icolor_t fcolor = sorted_edges[0]->color;
        icolor_t scolor = sorted_edges[sorted_edges.size() - 1]->color;
        cerr << "; FColor " << fcolor << " | SColor " << scolor << endl;

        icolor_t ccolor;
        if(fcolor == I_A && scolor == I_A) ccolor = I_A;
        else if(fcolor == I_B && scolor == I_B) ccolor = I_B;
        else ccolor = I_A;
        cerr << "; CColor " << ccolor << endl;
        if(ccolor == I_B)
        {
            cerr << "; Calling not S" << endl;
            conj.push(logic.mkNot(ISwap(pf)));
        }
        else
        {
            cerr << "; Calling I" << endl;
            conj.push(I(pf));
        }

        cerr << "; Itp: " << logic.printTerm(conj[conj.size() - 1]) << endl;
        divided = false;
        continue;
*/
        la = lb = lab = ra = rb = rab = false;
        if(l->color == I_A) la = true;
        else if(l->color == I_B) lb = true;
        else lab = true;
        if(r->color == I_A) ra = true;
        else if(r->color == I_B) rb = true;
        else rab = true;

      //  cerr << "; LA " << la << " | LB " << lb << " | LAB " << lab << endl;
      //  cerr << "; RA " << ra << " | RB " << rb << " | RAB " << rab << endl;
        assert(!((la && rb) || (lb && ra)));
        bool b = true;//rand() % 2;
        if(la || ra) // conflict in A, call I' or not S
        {
            assert(i == 0 || j == (factors.size() - 1));
            if(b && config.itp_euf_alg() == 4)
            {
                conj.push(Irec(pf, cache, h + 1));
            //    cerr << "; Calling I'" << endl;
            }
            else
            {
                conj.push(logic.mkNot(IprimeSwap(pf)));
          //      cerr << "; Calling S" << endl;
            }
        }
        else if(lb || rb) // conflict in B, call I or not S'
        {
            assert(i == 0 || j == (factors.size() - 1));
            if(b && config.itp_euf_alg() == 4)
            {
                conj.push(Irec(pf, cache, h + 1));
        //        cerr << "; Calling I" << endl;
            }
            else
            {
                conj.push(logic.mkNot(IprimeSwap(pf)));
      //          cerr << "; Calling S'" << endl;
            }
        }
        else // conflict has global endpoints
        {
            if(b && config.itp_euf_alg() == 4)
            {
                conj.push(Irec(pf, cache, h + 1));
    //            cerr << "; Calling I" << endl;
            }
            else
            {
                conj.push(logic.mkNot(IprimeSwap(pf)));
  //              cerr << "; Calling S'" << endl;
            }
        }
//        cerr << "; Itp: " << logic.printTerm(conj[conj.size() - 1]) << endl;
    }
    divided = false;
    }
    else
    {
        for(int i = 0; i < factors.size(); ++i)
            conj.push(Irec(factors[i], cache, h));
    }
  }

  PTRef res = logic.mkAnd(conj);
  //PTRef res = egraph.mkAnd( egraph.cons( conj ) );

  assert( res != PTRef_Undef);

  //cache[ p ] = res;

  //cerr << lstr << "Interpolant Irec(" << logic.printTerm(p.first->e) << "," << logic.printTerm(p.second->e) << ") = " << logic.printTerm(res) << endl;
  return res;
}

PTRef
CGraph::IrecSwap( const path_t & p, map< path_t, PTRef > & cache , unsigned int h)
{
    if(h > max_height) max_height = h;
  // True on empty path
  if ( p.first == p.second ) return logic.getTerm_true();

/*
  map< path_t, PTRef >::iterator it = cache.find( p );
  // Return previously computed value
  if ( it != cache.end( ) )
    return it->second;
*/

  string lstr(";");
  for(int i = 0; i < h; ++i) lstr += ' ';

#ifdef ITP_DEBUG
  cerr << lstr << "Interpolant IrecSwap(" << logic.printTerm(p.first->e) << "," << logic.printTerm(p.second->e) << ")" << endl;
#endif
  vec< PTRef > conj;
  vec< PTRef > conj_swap;
  // Will store factors
  vector< path_t > factors;
  factors.push_back( p );
  // Will store parents of A-path
  vector< path_t > parents;

  const bool a_factor = getFactorsAndParents( p, factors, parents );

  //if(!flat && parents.size() == 0) return interpolate_flat(p);

  if ( factors.size( ) == 1 )
  {
#ifdef ITP_DEBUG
    cerr << lstr << "Factor has size 1" << endl;
#endif
    // It's a B-path
    if ( !a_factor )
    {
#ifdef ITP_DEBUG
      cerr << lstr << "Single factor is a B-factor" << endl;
#endif
      // Compute J
      vector< path_t > b_premise_set;
      BSwap( p, b_premise_set );
      conj.push( J( p, b_premise_set ) );
#ifdef ITP_DEBUG
        cerr << lstr << "A-set has size " << b_premise_set.size() << endl;
#endif
        for ( unsigned i = 0 ; i < b_premise_set.size( ) ; i ++ )
        {
            path_t& fac = b_premise_set[i];
            assert(L.find(fac) != L.end());
#ifdef ITP_DEBUG
            cerr << "; Checking label of path (" << logic.printTerm(fac.first->e) << ", " << logic.printTerm(fac.second->e) << ") = " << L[fac] << endl;
#endif
            if(L[fac] == I_A)
            {
#ifdef ITP_DEBUG
                cerr << "; Not swapping" << endl;
#endif
                conj.push( IrecSwap( fac, cache, h + 1 ) );
            }
            else
            {
#ifdef ITP_DEBUG
                cerr << "; Swapping from S to (not I')" << endl;
#endif
                conj_swap.push(logic.mkNot(Iprime(fac)));
            }
        }
        if(conj_swap.size() > 0)
        {
            /*
            PTRef implicant = logic.mkNot(logic.mkEq(p.first->e, p.second->e));
            PTRef implicated = logic.mkAnd(conj_swap);
            conj.push(logic.mkImpl(implicant, implicated));
            */
            conj.push(logic.mkAnd(conj_swap));
        }
    }
    // It's an A-path
    else
    {
#ifdef ITP_DEBUG
        cerr << lstr << "Single factor is an A-factor" << endl;
#endif
      // Recurse on parents
      for ( unsigned i = 0 ; i < parents.size( ) ; i ++ )
      {
#ifdef ITP_DEBUG
          cerr << lstr << "Recursing on parent " << logic.printTerm(parents[i].first->e) << '-' << logic.printTerm(parents[i].second->e) << endl;
#endif
          conj.push( IrecSwap( parents[i], cache, h + 1) );
      }
    }
  }
  else
  {
//      divided = true;
    // Recurse on factors
   // if(!divided)
    if(factors.size() > 3 && config.itp_euf_alg() > 3)
    {
#ifdef ITP_DEBUG
    cerr << lstr << "Multiple factors for path (" << logic.printTerm(p.first->e) << "," << logic.printTerm(p.second->e) << ")" << endl;
    cerr << "Factors" << endl;
    for(int i = 0; i < factors.size(); ++i)
        cerr << " | " << logic.printTerm(factors[i].first->e) << '-' << logic.printTerm(factors[i].second->e) << endl;
#endif
    bool la, lb, lab, ra, rb, rab;
    divided = true;
    for(int i = 0; i < factors.size(); i += 3)
    {
        int j = i + 2;
        if(j >= factors.size()) j = (factors.size() - 1);

        path_t pf(factors[i].first, factors[j].second);
#ifdef ITP_DEBUG
        cerr << "; Subpath (" << logic.printTerm(pf.first->e) << "," << logic.printTerm(pf.second->e) << ")" << endl;
#endif
        CNode *l = pf.first;
        CNode *r = pf.second;

        vector<path_t> infactors;
        infactors.push_back(pf);
        vector<path_t> inparents;
        const bool a_factor = getFactorsAndParents(pf, infactors, inparents);
        if(j < (factors.size() - 1))
            assert(infactors.size() >= 3);
        if(infactors.size() >= 2)
        {
            if(!a_factor)
                conj.push(logic.mkNot(Iprime(pf)));
            else
                conj.push(IrecSwap(pf, cache, h + 1));
            continue;
        }

/*
        vector< CEdge * > sorted_edges;
        const size_t x_path_length = getSortedEdges(l, r, sorted_edges);

        icolor_t fcolor = sorted_edges[0]->color;
        icolor_t scolor = sorted_edges[sorted_edges.size() - 1]->color;
        cerr << "; FColor " << fcolor << " | SColor " << scolor << endl;

        icolor_t ccolor;
        if(fcolor == I_A && scolor == I_A) ccolor = I_A;
        else if(fcolor == I_B && scolor == I_B) ccolor = I_B;
        else ccolor = I_A;
        cerr << "; CColor " << ccolor << endl;
        if(ccolor == I_A)
        {
            cerr << "; Calling not S" << endl;
            conj.push(logic.mkNot(ISwap(pf)));
        }
        else
        {
            cerr << "; Calling I" << endl;
            conj.push(I(pf));
        }

        cerr << "; Itp: " << logic.printTerm(conj[conj.size() - 1]) << endl;
        divided = false;
        continue;
*/
        la = lb = lab = ra = rb = rab = false;
        if(l->color == I_A) la = true;
        else if(l->color == I_B) lb = true;
        else lab = true;
        if(r->color == I_A) ra = true;
        else if(r->color == I_B) rb = true;
        else rab = true;

    //    cerr << "; LA " << la << " | LB " << lb << " | LAB " << lab << endl;
      //  cerr << "; RA " << ra << " | RB " << rb << " | RAB " << rab << endl;
        assert(!((la && rb) || (lb && ra)));
        bool b = true;//rand() % 2;
        if(la || ra)
        {
            assert(i == 0 || j == (factors.size() - 1));
            if(b && config.itp_euf_alg() == 4)
            {
    //            cerr << "; Calling I'" << endl;
                conj.push(logic.mkNot(Iprime(pf)));
            }
            else
            {
      //          cerr << "; Calling S" << endl;
                conj.push(IrecSwap(pf, cache, h + 1));
            }
        }
        else if(lb || rb)
        {
            assert(i == 0 || j == (factors.size() - 1));
            if(b && config.itp_euf_alg() == 4)
            {
        //        cerr << "; Calling I'" << endl;
                conj.push(logic.mkNot(Iprime(pf)));
            }
            else
            {
          //      cerr << "; Calling S" << endl;
                conj.push(IrecSwap(pf, cache, h + 1));
            }
        }
        else // conflict has global endpoints
        {
            if(b && config.itp_euf_alg() == 4)
            {
            //    cerr << "; Calling I'" << endl;
                conj.push(logic.mkNot(Iprime(pf)));
            }
            else
            {
              //  cerr << "; Calling S" << endl;
                conj.push(IrecSwap(pf, cache, h + 1));
            }
        }
    }
    divided = false;
    }
    else
    {
#ifdef ITP_DEBUG
        cerr << "Multiple factors, recursing on them" << endl;
#endif
        for(int i = 0; i < factors.size(); ++i)
        {
#ifdef ITP_DEBUG
            cerr << "Recursing on factor " << logic.printTerm(factors[i].first->e) << '-' << logic.printTerm(factors[i].second->e) << endl;
#endif
            conj.push(IrecSwap(factors[i], cache, h));
        }
    }
  }

  PTRef res = logic.mkAnd(conj);
  //PTRef res = egraph.mkAnd( egraph.cons( conj ) );

  assert( res != PTRef_Undef);

  //cache[ p ] = res;

  //cerr << lstr << "Interpolant IrecSwap(" << logic.printTerm(p.first->e) << "," << logic.printTerm(p.second->e) << ") = " << logic.printTerm(res) << endl;
  return res;
}

void CGraph::B( const path_t & p
	      , vector< path_t > & b_premise_set )
{
  set< path_t > cache;
  Brec( p, b_premise_set, cache );
}

void CGraph::BSwap( const path_t & p
	      , vector< path_t > & a_premise_set )
{
  set< path_t > cache;
  BrecSwap( p, a_premise_set, cache );
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

void CGraph::BrecSwap( const path_t     & p
                 , vector< path_t > & a_premise_set
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
    if ( !a_factor )
    {
      for ( unsigned i = 0 ; i < parents.size( ) ; i ++ )
	    BrecSwap( parents[ i ], a_premise_set, cache );
    }
    // It's a B-path
    else
      a_premise_set.push_back( p );
  }
  else
  {
    // Recurse on factors
    for ( unsigned i = 0 ; i < factors.size( ) ; i ++ )
      BrecSwap( factors[ i ], a_premise_set, cache );
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
  if(sorted_edges.size() > max_width) max_width = sorted_edges.size();
  const bool a_factor = sorted_edges[ 0 ]->color == I_A;
  icolor_t last_color = sorted_edges[ 0 ]->color;
  x = 0 < x_path_length 
    ? sorted_edges[ 0 ]->target
    : sorted_edges[ 0 ]->source ;
  y = p.second;
  size_t i = 1;
  // Add parents
  if ( sorted_edges[ 0 ]->reason == PTRef_Undef )
  {
    CNode * tx = p.first;
    CNode * tn = x;
    assert( logic.getPterm(tx->e).size() == logic.getPterm(tn->e).size() );
    // Examine children of the congruence edge
    Pterm& px = logic.getPterm(tx->e);
    Pterm& pn = logic.getPterm(tn->e);
    for(int j = 0; j < px.size(); ++j)
    {
        PTRef arg_tx = px[j];
        PTRef arg_tn = pn[j];
      if ( arg_tn == arg_tx ) continue;
      // Add parents for further recursion
      parents.push_back( path( cnodes_store[ arg_tx ]
	                     , cnodes_store[ arg_tn ] ) );
      //assert(L.find(path(sorted_edges[0]->source, sorted_edges[0]->target)) != L.end());
      //L[ path(cnodes_store[arg_tx], cnodes_store[arg_tn]) ] = L[ path(sorted_edges[0]->source, sorted_edges[0]->target) ];
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
    if ( sorted_edges[ i ]->reason == PTRef_Undef )
    {
      assert( logic.getPterm(x->e).size() == logic.getPterm(n->e).size() );
      // Examine children of the congruence edge
      Pterm& px = logic.getPterm(x->e);
      Pterm& pn = logic.getPterm(n->e);
      for(int j = 0; j < px.size(); ++j)
      {
          PTRef arg_x = px[j];
          PTRef arg_n = pn[j];
	    if ( arg_n == arg_x ) continue;
    	// Add parents for further recursion
        parents.push_back( path( cnodes_store[ arg_x ]
	                       , cnodes_store[ arg_n ] ) );
        //assert(L.find(path(sorted_edges[i]->source, sorted_edges[i]->target)) != L.end());
      //L[ path(cnodes_store[arg_x], cnodes_store[arg_n]) ] = L[ path(sorted_edges[i]->source, sorted_edges[i]->target) ];
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

    labelFactors(factors);

  return a_factor;
}

void
CGraph::labelFactors(vector<path_t>& factors)
{
    // McMillan
    if(usingStrong())
        for(int i = 0; i < factors.size(); ++i)
            L[factors[i]] = I_B;

    // McMillan'
    else if(usingWeak())
        for(int i = 0; i < factors.size(); ++i)
            L[factors[i]] = I_A;

    // Random
    else if(usingRandom())
    {
        for(int i = 0; i < factors.size(); ++i)
        {
            if(rand() % 2)
            {
                //cerr << "; Labeling factor (" << logic.printTerm(factors[i].first->e) << ", " << logic.printTerm(factors[i].second->e) << ") = B" << endl;
                L[factors[i]] = I_B;
            }
            else
            {
                //cerr << "; Labeling factor (" << logic.printTerm(factors[i].first->e) << ", " << logic.printTerm(factors[i].second->e) << ") = A" << endl;
                L[factors[i]] = I_A;
            }
        }
    }
}

void
CGraph::verifyInterpolantWithExternalTool( const ipartitions_t& mask )
{
    if(interpolant == PTRef_Undef)
    {
        cerr << "; Error. Can't verify interpolant. Interpolant not computed yet" << endl;
        return;
    }

    cerr << "; Verifying partial interpolant" << endl;

    PTRef A = PTRef_Undef;
    PTRef B = PTRef_Undef;
    vec<PTRef> a_args;
    vec<PTRef> b_args;

    for(int i = 0; i < cedges.size(); ++i)
    {
        CEdge *ce = cedges[i];
        vec<PTRef> eq_args;
        if(ce->color == I_A)
        {
            eq_args.push(ce->source->e);
            eq_args.push(ce->target->e);
            a_args.push(logic.mkEq(eq_args));
        }
        else if(ce->color == I_B)
        {
            eq_args.push(ce->source->e);
            eq_args.push(ce->target->e);
            b_args.push(logic.mkEq(eq_args));
        }
    }
    PTRef dconf = logic.mkNot(logic.mkEq(conf1, conf2));
    if(conf_color == I_A)
        a_args.push(dconf);
    if(conf_color == I_B)
        b_args.push(dconf);
    A = logic.mkAnd(a_args);
    B = logic.mkAnd(b_args);

    /*
    cerr << ";CGraph edges inside verify: " << endl;
    vec<PTRef> ced;
    for(int i = 0; i < cedges.size(); ++i)
    {
        vec<PTRef> lala;
        lala.push(cedges[i]->source->e);
        lala.push(cedges[i]->target->e);
        PTRef lalaeq = logic.mkEq(lala);
        cerr << ';' << logic.printTerm(lalaeq) << " (" << cedges[i]->color << ") ";
        if(cedges[i]->reason == PTRef_Undef) cerr << "; (congruence)" << endl;
        else cerr << "; (basic)" << endl;
        //ced.push(logic.mkEq(lala));
    }
    //PTRef cand = logic.mkAnd(ced);
    //cerr << logic.printTerm(cand) << endl;

    cerr << ";Conflict: " << logic.printTerm(conf1) << " = " << logic.printTerm(conf2) << " has color " << conf_color << endl;
*/
    /*
    for(int i = 0; i < A_basic.size(); ++i)
    {
        //CEdge* ce = A_basic[i];
        //vec<PTRef> tmp, tmp2;
        //tmp.push(ce->source->e); tmp2.push(ce->target->e);
        //tmp.push(ce->target->e); tmp2.push(ce->source->e);
        //if(!logic.existsTermHash(logic.getSym_eq(), tmp) && !logic.existsTermHash(logic.getSym_eq(), tmp2))
        //    cerr << "ERROR, weird, basic A edge contains non original A equality" << endl;
        a_args.push(A_basic[i]);
    }
    A = logic.mkAnd(a_args);
    for(int i = 0; i < B_basic.size(); ++i)
    {
        //CEdge* ce = B_basic[i];
        //vec<PTRef> tmp, tmp2;
        //tmp.push(ce->source->e); tmp2.push(ce->target->e);
        //tmp.push(ce->target->e); tmp2.push(ce->source->e);
        //if(!logic.existsTermHash(logic.getSym_eq(), tmp) && !logic.existsTermHash(logic.getSym_eq(), tmp2))
        //    cerr << "ERROR, weird, basic B edge contains non original B equality" << endl;
        b_args.push(B_basic[i]);
    }
    B = logic.mkAnd(b_args);
*/
#ifdef ITP_DEBUG
    cerr << ";A: " << logic.printTerm(A) << endl;
    cerr << ";B: " << logic.printTerm(B) << endl;
#endif

    /*
    vec<PTRef> A;
    vec<PTRef> B;

    vec<PTRef>& assertions = logic.getAssertions();
    for(int i = 0; i < assertions.size(); ++i)
    {
        PTRef a = assertions[i];
        //if((logic.getIPartitions(a) & ~mask) != 0) A.push(a);
        if(isAstrict(logic.getIPartitions(a), mask)) A.push(a);
        else B.push(a);
    }
    */

    // Check A -> I, i.e., A & !I
    // First stage: print declarations
    const char * name_A = "verifyinterp_A.smt2";
    std::ofstream dump_out( name_A );
    logic.dumpHeaderToFile(dump_out);

    // Print only A atoms
    //for(int i = 0; i < A.size(); ++i)
    //    logic.dumpFormulaToFile(dump_out, A[i]);
    logic.dumpFormulaToFile(dump_out, A);
    //logic.dumpFormulaToFile(dump_out, logic.mkEq(conf1, conf2), true);
    logic.dumpFormulaToFile(dump_out, interpolant, true);
    dump_out << "(check-sat)" << endl;
    dump_out << "(exit)" << endl;
    dump_out.close( );
    // Check !
    bool tool_res;
    if ( int pid = fork() )
    {
      int status;
      waitpid(pid, &status, 0);
      switch ( WEXITSTATUS( status ) )
      {
	case 0:
	  tool_res = false;
	  break;
	case 1:
	  tool_res = true;
	  break;
	default:
	  perror( "Tool" );
	  exit( EXIT_FAILURE );
      }
    }
    else
    {
      execlp( "tool_wrapper.sh", "tool_wrapper.sh", name_A, NULL );
      perror( "Tool" );
      exit( 1 );
    }

    if ( tool_res == true )
    {
      //opensmt_error2( config.certifying_solver, " says A -> I does not hold" );
      cerr << "; Error, A -> I does not hold" << endl;
    }
    else
      cerr << "; A -> I holds" << endl;

    // Now check B & I
    const char * name_B = "verifyinterp_B.smt2";
    dump_out.open( name_B );
    logic.dumpHeaderToFile( dump_out );
    //vec<PTRef> and_args;
    //and_args.push(interpolant);
    //and_args.push(B);
    //PTRef iandb = logic.mkAnd(and_args);
    // Print only B atoms
    //for(int i = 0; i < B.size(); ++i)
    //    logic.dumpFormulaToFile(dump_out, B[i]);
    logic.dumpFormulaToFile(dump_out, interpolant);
    logic.dumpFormulaToFile(dump_out, B);
    //logic.dumpFormulaToFile(dump_out, iandb);
    //logic.dumpFormulaToFile(dump_out, logic.mkEq(conf1, conf2), true);
    dump_out << "(check-sat)" << endl;
    dump_out << "(exit)" << endl;
    dump_out.close( );
    // Check !
    if ( int pid = fork() )
    {
      int status;
      waitpid(pid, &status, 0);
      switch ( WEXITSTATUS( status ) )
      {
	case 0:
	  tool_res = false;
	  break;
	case 1:
	  tool_res = true;
	  break;
	default:
	  perror( "Tool" );
	  exit( EXIT_FAILURE );
      }
    }
    else
    {
      execlp( "tool_wrapper.sh", "tool_wrapper.sh", name_B, NULL );
      perror( "Tool" );
      exit( 1 );
    }
    if ( tool_res == true )
    {
      //opensmt_error2( config.certifying_solver, " says B & I does not hold" );
      cerr << "; Error B & I -> false does not hold" << endl;
    }
    else
      cerr << "; B & I -> false holds" << endl;
}

void CGraph::printAsDotty( ostream & os )
{
  os << "digraph cgraph {" << endl;
  // Print all nodes
  for ( map< PTRef, CNode * >::iterator it = cnodes_store.begin( ) 
      ; it != cnodes_store.end( )
      ; it ++ )
  {
    CNode * c = it->second;
    string color = "grey";
    if ( c->color == I_A ) color = "red";
    if ( c->color == I_B ) color = "blue";
    if ( c->color == I_AB ) color = "green";
    os << logic.getPterm(c->e).getId()
       << " [label=\""
       << logic.printTerm(c->e)
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
    os << logic.getPterm(c->source->e).getId( ) 
       << " -> " 
       << logic.getPterm(c->target->e).getId( ) 
       << " [color=\"" << color
       << "\",style=\"bold"
       << (c->reason == PTRef_Undef ? ",dashed" : "")
       << "\"]"
       << endl;
  }
  // Print conflict
  os << logic.printTerm(conf1)
     << " -> "
     << logic.printTerm(conf2)
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
