/*********************************************************************
Author: Edgar Pek <edgar.pek@lu.unisi.ch>
      , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch> 

OpenSMT -- Copyright (C) 2008, Roberto Bruttomesso

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

// Graph functions 
#ifndef DLGRAPH_H
#define DLGRAPH_H

#include <queue>
#include "Enode.h"
#include "Egraph.h"
#include "SMTConfig.h"

#define HASH_SET 0
#define LAZY_GENERATION 1

enum DL_sssp_direction { DL_sssp_forward, DL_sssp_backward };

// FIXME: 
// . constructor first
// . use reference when passing Numbers 
// . input parameters in constructor should have different names than class attributes
template <class T> struct DLVertex 
{
  DLVertex (  Enode * e_
           ,  int     id_ )
    : e             ( e_ )
    , id            ( id_ )
    , gamma         ( 0 )
    , pi            ( 0 )
    , old_pi        ( 0 ) 
    , dx            ( -1 )
    , dy            ( -1 )
    , dx_relevant   ( false )
    , dy_relevant   ( false )
    , dyn_outdegree ( 0 )
    , dyn_indegree  ( 0 )
    , h_outdegree   ( 0 ) 
    , h_indegree    ( 0 )
    , dist_from_src ( 0 )
    , dist_from_dst ( 0 )
  { }

  DLVertex ( DLVertex * v ) 
    : e		   ( v->e )
    , id	   ( v->id)
    , gamma	   ( v->gamma )
    , pi	   ( v->pi )
    , old_pi	   ( v->old_pi ) 
    , dx	   ( v->dx )
    , dy           ( v->dy )
    , dx_relevant  ( v->dx_relevant )
    , dy_relevant  ( v->dy_relevant )
    , dyn_outdegree( v->dyn_outdegree )
    , dyn_indegree ( v->dyn_indegree ) 
    , h_outdegree  ( v->h_outdegree )
    , h_indegree   ( v->h_indegree ) 
    , dist_from_src( v->dist_from_src )
    , dist_from_dst( v->dist_from_dst )
  { }

  inline T &  getDist( DL_sssp_direction go )	    { return ( go == DL_sssp_forward ) ? dx : dy; } 
  inline void setDist( DL_sssp_direction go, T val) { if     ( go == DL_sssp_forward ) dx = val; else dy = val; }

  inline bool getRelevancy( DL_sssp_direction go           ) { return go == DL_sssp_forward ? dx_relevant : dy_relevant; }
  inline void setRelevancy( DL_sssp_direction go, bool val ) { if   ( go == DL_sssp_forward ) dx_relevant = val; else dy_relevant = val; }

  inline void setDistFrom( DL_sssp_direction go, T val ) { ( go == DL_sssp_forward ) ? dist_from_src = val : dist_from_dst = val;  }
  inline T &  getDistFrom( DL_sssp_direction go )        { return ( go == DL_sssp_forward ) ? dist_from_src : dist_from_dst; }

  struct gammaGreaterThan
  {
    inline bool operator ( )( DLVertex * x, DLVertex * y ) 
    {
      return x->gamma > y->gamma;	
    }
  };

  struct ssspGreaterThan
  {
    ssspGreaterThan( DL_sssp_direction go_ ) : go (go_) { }
    inline bool operator ( )( DLVertex * x, DLVertex * y )
    {
      return ( go == DL_sssp_forward ) ? ( x->dx > y->dx ) : ( x->dy > y->dy );
    }
    DL_sssp_direction go;
  };

  struct ssspDxGreaterThan
  {
    inline bool operator ( )( DLVertex * x, DLVertex * y )
    {
      return  x->dx > y->dx ;
    }
  };

  struct ssspDyGreaterThan
  {
    inline bool operator ( )( DLVertex * x, DLVertex * y )
    {
      return  x->dy > y->dy ;
    }
  };

  Enode *     e;
  const int   id;
  T	      gamma;
  T	      pi;
  T	      old_pi;
  T	      dx;
  T	      dy;
  bool        dx_relevant;
  bool        dy_relevant;
  size_t      dyn_outdegree;
  size_t      dyn_indegree;
  size_t      h_outdegree;
  size_t      h_indegree;
  T	      dist_from_src;
  T	      dist_from_dst;
};

template <class T> struct DLEdge 
{

  DLEdge( Enode *    c_
	, int        id_
        , DLVertex<T> * u_
	, DLVertex<T> * v_
	, T     & wt_ )
      : c  ( c_   )
      , id ( id_  )
      , u  ( u_   )
      , v  ( v_   )
      , wt ( wt_  ) 
      , rwt( -1   )
      , r  ( NULL ) // TODO: check if needed
  { }

  inline void printDLEdge( ostream &os ) { os << u->e << " --[" << wt << "]--> " << v->e; }
  inline friend ostream & operator<<( ostream & os, DLEdge * e ) { assert( e ); e->printDLEdge( os ); return os; }

  Enode *       c;    // reference to the original Enode
  const int     id;   // id of the edge
  DLVertex<T> * u;    // the source vertex
  DLVertex<T> * v;    // the destination vertex
  const T       wt;   // original cost of the edges
  T             rwt;  // reduced  cost of the edge (nonnegative edge weight)
  DLEdge *      r;    // the edge that caused deduction TODO: check if needed!
};

template <class T> struct DLComplEdges
{
  DLComplEdges ( DLEdge<T> * pos_
	       , DLEdge<T> * neg_ ) 
	     : pos ( pos_ )
	     , neg ( neg_ )  
  { }

  DLEdge<T> *pos;
  DLEdge<T> *neg;
};

template <class T> struct DLTwoVertices
{
  DLTwoVertices ( DLVertex<T> * u_
		, DLVertex<T> * v_ )
	       : u ( u_ )
	       , v ( v_ )
  { }

  struct vertexIdGreaterThan
  {
    inline bool operator ( ) ( const DLTwoVertices<T> & x, const DLTwoVertices<T> & y)
    {
      return x.u->id > y.u->id;
    }

  };

  DLVertex<T> * u;
  DLVertex<T> * v;
};

namespace __gnu_cxx
{
  // Hash function for DLEdge *
  template< typename DLEdge >
  struct SizeTDLEdge
  {
    size_t operator ( ) ( const DLEdge & e   ) const 
    {
      return (size_t) e;
    }
  };

}

template< class T > class DLGraph
{
public:

    DLGraph( SMTConfig & config_, Egraph & egraph_ ) 
      : Vcnt		   ( 0 ) 
      , Ecnt		   ( 0 )
      , active_pi_prime	   ( false )
      , pi_prime_count	   ( 0 )
      , active_gamma	   ( false )
      , gamma_count	   ( 0 )
      , active_rwt	   ( false )
      , rwt_count	   ( 0 )
      , active_dist	   ( false )
      , dist_count	   ( 0 )
      , active_final_dist  ( false )
      , final_dist_count   ( 0 )
      , active_dx_rel      ( false )
      , dx_rel_count       ( 0 )
      , active_dy_rel      ( false )
      , dy_rel_count       ( 0 )				  
      , active_dfs_visited ( false )
      , dfs_visited_count  ( 0 )
      , active_dfs_finished( false )
      , dfs_finished_count ( 0 )
      , active_apsp_inf    ( false )
      , apsp_inf_count     ( 0 )
      , max_dist_from_src  ( 0 )
      , max_dist_from_dst  ( 0 )
      , max_adj_list_size  ( 0 )
      , max_dyn_vertex_id  ( 0 )
      , max_dyn_edges      ( 0 )
      , after_backtrack    ( false )
      , config             ( config_ )
      , egraph             ( egraph_ )
  { } 

   ~DLGraph( );

  typedef vector< DLEdge<T> * > AdjList;

  typedef __gnu_cxx::SizeTDLEdge< const DLEdge<T> * > HashDLEdge;
  typedef vector< DLEdge<T> * >                       DLPath;

  typedef map< Enode *, DLVertex<T> * >	  Enode2Vertex;
  typedef map< Enode *, DLComplEdges<T> > Enode2Edge;

  inline unsigned getVcnt ( ) const { return Vcnt; }
  inline unsigned getEcnt ( ) const { return Ecnt; }

  inline Enode2Edge &            getEdgeMap        ( ) { return edgeMap; }
  inline vector< AdjList > &     getDAdj           ( ) { return dAdj; }
  inline vector< DLEdge<T> * > & getConflictEdges  ( ) { return conflict_edges; }
  inline DLVertex<T> *           getNegCycleVertex ( ) { return negCycleVertex; }
  inline double                  getDynGraphDensity( ) { return (double) dEdges.size( ) / (double) Vcnt; }

  inline void deleteFromAdjList( AdjList & adj_list, DLEdge<T> * e)
  { 
    assert( e ); 
    typename AdjList::iterator it = find( adj_list.begin( ), adj_list.end( ), e );
    if ( it != adj_list.end( ))
      adj_list.erase( it );
  }

  void        insertStatic  ( Enode * );
  DLEdge<T> * insertDynamic ( Enode *, bool reason );
  void	      insertImplied ( Enode * );
  void	      insertInactive( Enode * );

  void	      deleteActive  ( Enode * );
  void	      deleteInactive( Enode * );

  inline DLEdge<T> * getOppositePolarityEdge( Enode * c ) { assert( c->hasPolarity( ) );  assert( edgeMap.find( c ) != edgeMap.end( ) );    DLComplEdges<T> edges = edgeMap.find( c )->second;     DLEdge<T> * e = c->getPolarity( ) == l_True ? edges.neg : edges.pos;  assert( e ); return e;  }
  inline DLEdge<T> * getEdgeWithPolarity    ( Enode * c ) { assert( c->hasPolarity( ) );  assert( edgeMap.find( c ) != edgeMap.end( ) );    DLComplEdges<T> edges = edgeMap.find( c )->second;     DLEdge<T> * e = c->getPolarity( ) == l_True ? edges.pos : edges.neg;  assert( e ); return e;  }

  inline void updateDynDegree( DLEdge<T> * e )
  {
    e->u->dyn_outdegree = dAdj[    e->u->id ].size( );
    e->v->dyn_indegree  = dAdjInc[ e->v->id ].size( );
  }

  inline void updateHDegree( DLEdge<T> * e )
  {
    e->u->h_outdegree = hAdj[    e->u->id ].size( );
    e->v->h_indegree  = hAdjInc[ e->v->id ].size( );
  }

  // DFS visit - check for the cycle
  bool	      dfsVisit( DLEdge<T> * ); 

  bool        checkNegCycle    ( Enode *, bool );
  bool        checkNegCycleDFS ( Enode *, bool );
  void	      findHeavyEdges( Enode * );
  void	      iterateInactive( DLEdge<T> * );

  inline bool isParallelAndHeavy( DLEdge<T> *e )
  {
    // Check if there is a parallel edge of smaller weight - if yes: return
    AdjList & adj_list_x = dAdj[ e->u->id ];
    for ( typename AdjList::iterator it = adj_list_x.begin( ); it != adj_list_x.end( ); ++ it )
      if ( ( (*it)->v->id == e->v->id ) && ( (*it)->wt < e->wt )  )
	return true;
    return false;
  }

  inline void addIfHeavy( const T & rpath_wt, DLEdge<T> * e, DLEdge<T> *edge ) 
  {
    assert ( ! e->c->hasPolarity( ) && ! e->c->isDeduced( ) );
    if ( rpath_wt + e->v->pi - e->u->pi <= e->wt )
    {
      if ( isGreedy( ) )
      {
        e->r = edge;
	if ( findShortestPath( e ) )               // added for eager_lazy schema
	{	
	  heavy_edges.push_back( e );
	  undo_stack_deduced_edges.push_back( e ); // added for eager_lazy schema
	}
      }
      else
	heavy_edges.push_back( e );
    }
  }

  void	          findHeavyEdgesFW  ( Enode *  );  // find heavy edges with the Floyd-Warshall's algorithm
  void	          iterateInactiveFW ( );	   // iterate through the set of inactive edges

  inline DLPath & getShortestPath   ( DLEdge<T> *e ) { assert( e ); return shortest_paths[ e->id ]; }
  inline void     clearShortestPath ( DLEdge<T> *e ) { assert( e ); shortest_paths[ e->id ].clear( ); clearSPTs( ); }

  inline void     computeModel      ( );

  void        printAdj      ( vector<AdjList> & );
  void        printAdjList  ( AdjList & );
  
  inline void printStatAdj ( ) { printAdj(sAdj); }
  inline void printDynAdj  ( ) { printAdj(dAdj); }

  Real tmp_edge_weight;
  
  vector< DLVertex<T> * > vertices;
  vector< DLEdge<T> * >   heavy_edges;              // TODO: deal with it when backtracking!

  vector< Enode *  >    undo_stack_inactive_enodes; //  stack of inactive edges
  vector< DLEdge<T> * > undo_stack_deduced_edges;   //  stack of deduced edges

  void printShortestPath ( DLEdge<T> *, const char * );
  void printDLPath       ( DLPath, const char * );

  //
  // FIXME: This is a trick to deactivate LAZY_GENERATION for
  // RDL. It seems that is is faster this way ...
  //
  inline bool isGreedy( )
  {
    return ( 0 == LAZY_GENERATION || config.logic == QF_RDL );
  }
private:

  inline DLVertex<T> * getDLVertex( Enode * x )   
  {	
    if ( vertexMap.find( x ) == vertexMap.end( ) )
    {
      DLVertex<T> * v = new DLVertex<T>( x, vertexMap.size( ) );
      vertexMap.insert( pair< Enode *, DLVertex<T> *> (x, v) );	
      vertices.resize( vertexMap.size( ) ); vertices[v->id] = v;
      return v;
    }

    return vertexMap.find( x )->second;
  }

  DLComplEdges<T> getDLEdge( Enode * );

  inline Real & getPosWeight ( Real & weight ) { (void)weight; return tmp_edge_weight; }
  inline long & getPosWeight ( long & weight ) 
  { 
    weight = atol( tmp_edge_weight.get_str( ).c_str( ) ); 
    return weight; 
  }

  // Fast pi prime update check. Cannot be nested!
  inline void initPiPrime   ( )		        { assert( !active_pi_prime ); active_pi_prime = true; pi_primes.resize( Vcnt, pi_prime_count ); ++ pi_prime_count; }
  inline void updatePiPrime ( DLVertex<T> * v ) { assert(  active_pi_prime ); assert( v->id < (int)pi_primes.size( ) ); pi_primes[ v->id ] = pi_prime_count; }
  inline bool isPiPrime     ( DLVertex<T> * v ) { assert(  active_pi_prime ); assert( v->id < (int)pi_primes.size( ) ); return pi_primes[ v->id ] == pi_prime_count; }
  inline void donePiPrime   ( )		        { assert(  active_pi_prime ); active_pi_prime = false; }

  // Fast gamma update check. Cannot be nested.
  inline void initGamma   ( )		      { assert( !active_gamma ); active_gamma = true; gammas.resize( Vcnt, gamma_count ); ++ gamma_count; }
  inline void readGamma   ( DLVertex<T> * v ) { assert(  active_gamma ); assert( v->id < (int)gammas.size( ) ); gammas[ v->id ] = gamma_count; }
  inline bool isGammaRead ( DLVertex<T> * v ) { assert(  active_gamma ); assert( v->id < (int)gammas.size( ) ); return gammas[ v->id ] == gamma_count; }
  inline void doneGamma   ( )		      { assert(  active_gamma ); active_gamma = false; }

  // Fast rwt update check. Cannot be nested.
  inline void initRwt     ( )		    { assert( !active_rwt ); active_rwt = true; rwts.resize( Ecnt, rwt_count); rwt_count ++;}
  inline void updateRwt   ( DLEdge<T> * e ) { assert(  active_rwt ); assert( e->id < (int)rwts.size( ) ); rwts[ e->id ] = rwt_count; }
  inline bool isRwtValid  ( DLEdge<T> * e ) { assert(  active_rwt ); assert( e->id < (int)rwts.size( ) ); return rwts[ e->id ] == rwt_count; }
  inline void doneRwt     ( )		    { assert(  active_rwt ); active_rwt = false; }

  // Fast distance update check. Cannot be nested.
  inline void initDist   ( )		     { assert( !active_dist ); active_dist = true; dists.resize( Vcnt, dist_count ); ++ dist_count; }
  inline void readDist   ( DLVertex<T> * v ) { assert(  active_dist ); assert( v->id < (int)dists.size( ) ); dists[ v->id ] = dist_count; }
  inline bool isDistRead ( DLVertex<T> * v ) { assert(  active_dist ); assert( v->id < (int)dists.size( ) ); return dists[ v->id ] == dist_count; }
  inline void doneDist   ( )		     { assert(  active_dist ); active_dist = false; }

  // Fast final distance check. Cannot be nested.
  inline void initFinalDist ( )                 { assert( !active_final_dist ); active_final_dist = true; final_dists.resize( Vcnt, final_dist_count ); ++ final_dist_count; }
  inline void finalDist	    ( DLVertex<T> * v ) { assert(  active_final_dist ); assert( v->id < (int)final_dists.size( ) ); final_dists[ v->id ] = final_dist_count; }
  inline bool isDistFinal   ( DLVertex<T> * v ) { assert(  active_final_dist ); assert( v->id < (int)final_dists.size( ) ); return final_dists[ v->id ] == final_dist_count; }
  inline void doneFinalDist ( )		        { assert(  active_final_dist ); active_final_dist = false; }

  // Fast dx relevancy check. Cannot be nested.
  inline void initDxRel    ( )                 { assert ( !active_dx_rel ); active_dx_rel = true; dx_rels.resize( Vcnt, dx_rel_count ); ++ dx_rel_count; }
  inline void updateDxRel  ( DLVertex<T> * v ) { assert (  active_dx_rel ); assert( v->id < (int)dx_rels.size( ) ); dx_rels[ v->id ] = dx_rel_count; }
  inline bool isDxRelValid ( DLVertex<T> * v ) { assert (  active_dx_rel ); assert( v->id < (int)dx_rels.size( ) ); return dx_rels[ v->id ] == dx_rel_count; }
  inline void doneDxRel    ( )                 { assert (  active_dx_rel ); active_dx_rel = false; }

  // Fast dy relevancy check. Cannot be nested.
  inline void initDyRel    ( )                 { assert ( !active_dy_rel ); active_dy_rel = true; dy_rels.resize( Vcnt, dy_rel_count ); ++ dy_rel_count; }
  inline void updateDyRel  ( DLVertex<T> * v ) { assert (  active_dy_rel ); assert( v->id < (int)dy_rels.size( ) ); dy_rels[ v->id ] = dy_rel_count; }
  inline bool isDyRelValid ( DLVertex<T> * v ) { assert (  active_dy_rel ); assert( v->id < (int)dy_rels.size( ) ); return dy_rels[ v->id ] == dy_rel_count; }
  inline void doneDyRel    ( )                 { assert (  active_dy_rel ); active_dy_rel = false; }

  // Fast dfs visited check. Cannot be nested.
  inline void initDfsVisited ( )	         { assert ( !active_dfs_visited ); active_dfs_visited = true; dfs_visited.resize( Vcnt, dfs_visited_count ); ++ dfs_visited_count; }
  inline void setDfsVisited  ( DLVertex<T> * v ) { assert (  active_dfs_visited ); assert( v->id < (int) dfs_visited.size( ) ); dfs_visited[ v->id ] = dfs_visited_count; }
  inline bool isDfsVisited   ( DLVertex<T> * v ) { assert (  active_dfs_visited ); assert( v->id < (int) dfs_visited.size( ) ); return dfs_visited[ v->id ] == dfs_visited_count; }
  inline void doneDfsVisited ( )	         { assert (  active_dfs_visited ); active_dfs_visited = false; }

  // Fast dfs finished check. Cannot be nested.
  inline void initDfsFinished ( )	          { assert ( !active_dfs_finished ); active_dfs_finished = true; dfs_finished.resize( Vcnt, dfs_finished_count ); ++ dfs_finished_count; }
  inline void setDfsFinished  ( DLVertex<T> * v ) { assert (  active_dfs_finished ); assert( v->id < (int) dfs_finished.size( ) ); dfs_finished[ v->id ] = dfs_finished_count; }
  inline bool isDfsFinished   ( DLVertex<T> * v ) { assert (  active_dfs_finished ); assert( v->id < (int) dfs_finished.size( ) ); return dfs_finished[ v->id ] == dfs_finished_count; }
  inline void doneDfsFinished ( )	          { assert (  active_dfs_finished ); active_dfs_finished = false; }

  // Fast infinity distance check in apsp distance matrix. Cannot be nested.
  inline void initInfAPSP   ( )		      { assert ( !active_apsp_inf ); active_apsp_inf = true; apsp_infs.resize( Vcnt ); for( unsigned i = 0; i < Vcnt; ++i ) apsp_infs[i].resize(Vcnt, apsp_inf_count ); ++ apsp_inf_count; }
  inline void updateAPSP    ( int i, int j )  { assert (  active_apsp_inf ); assert( i < (int) apsp_infs.size( ) ); assert( j < (int) apsp_infs[ i ].size( ) ); apsp_infs[ i ][ j ] = apsp_inf_count; }
  inline void invalidateAPSP( int i, int j )  { assert (  active_apsp_inf ); assert( i < (int) apsp_infs.size( ) ); assert( j < (int) apsp_infs[ i ].size( ) ); apsp_infs[ i ][ j ] = 0; }
  inline bool isValidAPSP   ( int i, int j )  { assert (  active_apsp_inf ); assert( i < (int)apsp_infs.size( ) ); assert( j < (int)apsp_infs[ i ].size( ) ); return apsp_infs[ i ][ j ] == apsp_inf_count; }
  inline void doneInfAPSP   ( )		      { assert (  active_apsp_inf ); active_apsp_inf = false; }

  // Dotty pretty print
  void printDynGraphAsDotty( const char *, DLEdge<T> *e = NULL );
  inline void printEdgeWPi ( ofstream & out, DLEdge<T> * e)
  {
    assert( e );
    out << "\"" << e->u->e << " | " << e->u->pi << "\"" 
        << " -> " 
	<< "\"" << e->v->e << " | " << e->v->pi << "\"" 
	<< " [label=" << e->wt << "];" << endl;
  }
  void printSSSPAsDotty( const char * , DLVertex<T> * , DL_sssp_direction );
  inline void printSSSPEdge( ofstream & out, DLEdge<T> * e, DL_sssp_direction direction) 
  { 
    assert( e );
    DLVertex<T> * u = ( direction == DL_sssp_forward ) ? e->u : e->v;
    DLVertex<T> * v = ( direction == DL_sssp_forward ) ? e->v : e->u;
    string attrib_u, attrib_v;
    const bool valid_delta_u = ( direction == DL_sssp_forward ) ? isDxRelValid( u ) : isDyRelValid( u );
    const bool valid_delta_v = ( direction == DL_sssp_forward ) ? isDxRelValid( v ) : isDyRelValid( v );

    attrib_u = ( valid_delta_u && u->getRelevancy( direction ) ) ? " [style=filled, fillcolor=gray] " : "";
    attrib_v = ( valid_delta_v && v->getRelevancy( direction ) ) ? " [style=filled, fillcolor=gray] " : "";
    
    out << "\"" << u->e << " | " << u->getDist( direction ) << "\"" << attrib_u << endl;
    out << "\"" << v->e << " | " << v->getDist( direction ) << "\"" << attrib_v << endl;

    out << "\"" << u->e << " | " << u->getDist( direction )  << "\"" 
        << " -> " 
	<< "\"" << v->e << " | " << v->getDist( direction ) <<  "\"" 
	<< " [label=" << e->wt << "];" << endl;
  }

  inline void printDistEdge( ofstream & out, DLEdge<T> * e, string attrib = ";" ){
    assert( out );
    assert( e   );
    out << "\"" << e->u->e << " | " << e->u->dy << "\"" 
      << " -> " 
      << "\"" << e->v->e << " | " << e->v->dx << "\"" 
      << " [label=" << e->wt << "] " << attrib << endl;
  }

  inline void printPlainEdge( ofstream & out, DLEdge<T> * e, string attrib = ";" ){
    assert( out );
    assert( e   );
    out << "\"" << e->u->e << " | " << e->u->id << "\"" 
        << " -> " 
        << "\"" << e->v->e << " | " << e->v->id <<  "\"" 
        << " [label=" << e->wt << "] " << attrib << endl;
  }

  void printInactiveAsDotty( const char * );
  void printDeducedAsDotty(  const char * );

  void printAdjMatrix( const char * );
  void printAPSPMatrix( const char * );

  //  SSSP computation
  void findSSSP( DLVertex<T> *, DL_sssp_direction );
  inline void insertRelevantVertices( DLVertex<T> * v, DL_sssp_direction go )
  { 
    if( go == DL_sssp_forward )
    {
      assert( isDxRelValid( v ) && v->dx_relevant );
      dx_relevant_vertices.push_back( v );
      total_in_deg_dx_rel += hAdjInc[ v->id ].size( );
    }
    else
    {
      assert( isDyRelValid( v ) && v->dy_relevant );
      dy_relevant_vertices.push_back( v );  
      total_out_deg_dy_rel += hAdj[ v->id ].size( );
    }
  }

  inline void pushPBheap( DL_sssp_direction go, DLVertex<T> * v )
  { 
    if ( go == DL_sssp_forward )
    {
      assert( v->id < (int)pq_dx_it.size( ) );
      pq_dx_it[ v->id ] = pq_dx.push( v );
    }
    else
    {
      assert( v->id < (int)pq_dy_it.size( ) );
      pq_dy_it[ v->id ] = pq_dy.push( v );
    }
  }
  inline bool emptyPBheap( DL_sssp_direction go )
  {
    return ( go == DL_sssp_forward ) ? pq_dx.empty ( ) 
				     : pq_dy.empty( ) ;
  }

  inline DLVertex<T> * topPBheap( DL_sssp_direction go )
  {
    return ( go == DL_sssp_forward ) ? pq_dx.top( ) 
				     : pq_dy.top( );
  }

  inline void popPBheap( DL_sssp_direction go )
  {
    (go == DL_sssp_forward ) ? pq_dx.pop( ) : pq_dy.pop( );
  }

  inline void modifyPBheap( DL_sssp_direction go, DLVertex<T> * v )
  {
    ( go == DL_sssp_forward ) ? pq_dx.modify( pq_dx_it[ v->id ], v ) 
			      : pq_dy.modify( pq_dy_it[ v->id ], v );
  }

  inline void clearPBheap ( DL_sssp_direction go )
  {
    ( go == DL_sssp_forward ) ? pq_dx.clear( ) : pq_dy.clear( );
  }
    
  inline size_t sizePBheap( DL_sssp_direction go )
  {
    return ( go == DL_sssp_forward ) ? pq_dx.size( ) : pq_dy.size( );
  }

  inline void addToNewSpaths( int i, int j )
  {
    assert( vertices[i]->id == i && vertices[j]->id == j );
    new_spaths.insert( DLTwoVertices<T>( vertices[i], vertices[j] ) );
  }
  void               updateSPT ( DLEdge<T> * e, DL_sssp_direction go );
  inline DLEdge<T> * getSPT    ( DLVertex<T> * v, DL_sssp_direction go ) { assert( v ); return ( go == DL_sssp_forward ) ? fSPT[ v->id ] : bSPT[ v->id ]; }
  inline void        clearSPTs ( ) { bSPT.clear( ); bSPT.resize( Vcnt ); fSPT.clear( ); fSPT.resize( Vcnt ); }

  inline void        updateFringe( DLEdge<T> * e, DL_sssp_direction go) { assert( e ); (go == DL_sssp_forward ) ? fFringe[ e->u->id ] = e : bFringe[ e->u->id ] = e; }
  inline DLEdge<T> * getFringe   ( DLVertex<T> * v, DL_sssp_direction go) { assert( v ); return ( go == DL_sssp_forward ) ? fFringe[ v->id ] : bFringe[ v->id ]; }

  // find shortest path for an edge
  bool findShortestPath( DLEdge<T> * );
  
  unsigned Vcnt;
  unsigned Ecnt;
	
  bool		active_pi_prime;    // To prevent nested usage
  vector< int > pi_primes;	    // Fast pi prime update checking
  int		pi_prime_count;	    // New pi prime token

  bool		active_gamma;	    // To prevent nested usage
  vector< int > gammas;		    // Fast check if gamma was updated
  int		gamma_count;	    // New gamma token

  bool		active_rwt;	    // To prevent nested usage
  vector< int > rwts;		    // Fast chek if rwt was updated
  int           rwt_count;	    // New rwt token

  bool	        active_dist;	    // To prevent nested usage
  vector< int > dists;		    // Fast check if dx was updated
  int           dist_count;         // New dist token

  bool          active_final_dist;  // To prevent nested usage
  vector< int > final_dists;	    // Fast check if dist is final
  int           final_dist_count;   // New final dist token

  bool          active_dx_rel;	    // To prevent nested usage
  vector< int > dx_rels;            // Fast check if dx is relevant
  int           dx_rel_count;       // DeltaX relevancy token

  bool          active_dy_rel;      // To prevent nested usage
  vector< int > dy_rels;            // Fast check if dy is relevant
  int           dy_rel_count;       // DeltaY relevancy token

  // for DFS
  bool		active_dfs_visited; // To prevent nested usage
  vector< int > dfs_visited;	    // Fast check if a vertex is visited during dfs
  int		dfs_visited_count;  // dfs visted token

  bool		active_dfs_finished; // To prevent nested usage
  vector< int > dfs_finished;	     // Fast check if processing of vertex is finished
  int		dfs_finished_count;  // dfs finished count

  bool			  active_apsp_inf; // To prevent nested usage
  vector< vector< int > > apsp_infs;       // Fast check if a value in apsp matrix is infinity
  int			  apsp_inf_count;  // Apsp infinity check token


  Enode2Vertex          vertexMap;
  Enode2Edge            edgeMap;
  vector< AdjList >     sAdj;	   // adjacency list - static constraint graph
  vector< DLEdge<T> * > sEdges;    // edges - static constraint graph

  vector< AdjList >     dAdj;      // adjacency list - dynamic constraint graph
  vector< AdjList >     dAdjInc;   // incoming edges adjacency list  - dynamic constraint graph
  vector< DLEdge<T> * > dEdges;    // edges - dynamic constraint graph

  vector< AdjList >     iAdj;      // adjacency list - implied graph
  vector< DLEdge<T> * > iEdges;    // edges - implied graph

  vector< AdjList  >    hAdj;
  vector< AdjList  >    hAdjInc;
  vector< DLEdge<T> * > hEdges;	   // the vector of inactive edges :  d - s

  vector< DLEdge<T> * > conflict_edges;	// used to explain a conflict
  DLVertex<T> *         negCycleVertex;

  vector< DLVertex<T> * > vertex_heap;
  vector< DLVertex<T> * > changed_vertices;

  // data structures used in SSSP computations
  vector< DLVertex<T> * > dist_heap;    // min-heap of distances
  typedef priority_queue< DLVertex<T> *, typename DLVertex<T>::ssspDxGreaterThan, pairing_heap_tag > pq_dx_type;
  pq_dx_type pq_dx;
  vector< typename pq_dx_type::point_iterator > pq_dx_it;
  typedef priority_queue< DLVertex<T> *, typename DLVertex<T>::ssspDyGreaterThan, pairing_heap_tag > pq_dy_type;
  pq_dy_type pq_dy;
  vector< typename pq_dy_type::point_iterator > pq_dy_it;

  // data structures used in APSP computations
  set< DLTwoVertices<T>, typename DLTwoVertices<T>::vertexIdGreaterThan > new_spaths;	  // new shortest paths

  // used to explain deduction - i.e. to get a reason for a deduction
  vector< DLEdge<T> * > bSPT;		// backward shortest path tree
  vector< DLEdge<T> * > fSPT;		// forward  shortest path tree
  vector< DLEdge<T> * > bFringe;	// backward fringe  
  vector< DLEdge<T> * > fFringe;	// forward  fringe

  vector< DLPath >      shortest_paths; // shortest path for an edge 

  vector< DLVertex<T> * > dx_relevant_vertices;
  vector< DLVertex<T> * > dy_relevant_vertices;

  // for dfs
  vector< DLVertex<T> * > dfs_stack;
  vector< DLEdge<T> * > cycle_edges;

  unsigned total_in_deg_dx_rel;
  unsigned total_out_deg_dy_rel;

  T        max_dist_from_src;
  T        max_dist_from_dst;

  unsigned max_adj_list_size;
  unsigned max_dyn_vertex_id;
  unsigned max_dyn_edges;

  bool	   after_backtrack;

  SMTConfig & config;
  Egraph &    egraph;
};

#endif
