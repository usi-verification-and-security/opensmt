/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008 - 2012 Roberto Bruttomesso

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
/* Based on the paper
 * @article{DBLP:journals/corr/abs-1111-5652,
 *    author    = {Alexander Fuchs and Amit Goel and Jim Grundy and Sava Krstic and
 *                 Cesare Tinelli},
 *    title     = {Ground interpolation for the theory of equality},
 *    journal   = {Logical Methods in Computer Science},
 *    volume    = {8},
 *    number    = {1},
 *    year      = {2012},
 *    ee        = {http://dx.doi.org/10.2168/LMCS-8(1:6)2012},
 *    bibsource = {DBLP, http://dblp.uni-trier.de}
 *  }
 */

#ifdef PRODUCE_PROOF

#ifndef UF_INTERPOLATOR_H
#define UF_INTERPOLATOR_H

#include "Enode.h"
#include "SMTConfig.h"

struct CEdge;

struct CNode
{
  CNode( const int id_
       , Enode *   e_ )
    : id    ( id_ )
    , e     ( e_ )
    , color ( I_UNDEF )
    , next  ( NULL )
  {
    assert( id == e->getId( ) );
  }

  const int id;
  Enode *   e;
  icolor_t color;
  CEdge *   next;
};

typedef pair< CNode *, CNode * > path_t;

struct CEdge
{
  CEdge ( CNode * s
        , CNode * t
        , Enode * r )
    : source( s )
    , target( t )
    , reason( r )
    , color ( I_UNDEF )
  {
    assert( source );
    assert( target );
  }

  CNode * source;
  CNode * target;
  Enode * reason;
  icolor_t color;

  inline friend ostream & operator<<( ostream & os, CEdge * ce )
  {
    return os << ce->source->e << " ---> " << ce->target->e;
  }
};

class Egraph;

class CGraph
{
public:

  CGraph( Egraph & egraph_
        , SMTConfig & config_ )
    : egraph  ( egraph_ )
    , config  ( config_ )
    , colored ( false )
    , conf1   ( NULL )
    , conf2   ( NULL )
    , conf    ( NULL )
  { }

  ~CGraph( ) { clear( ); }

  void     addCNode      ( Enode * );
  void     addCEdge      ( Enode *, Enode *, Enode * );
  void     revertEdges   ( CNode * );
  Enode *  getInterpolant( const ipartitions_t & );
  void     printAsDotty  ( ostream & );

  inline void setConf( Enode * c1, Enode * c2, Enode * r )
  {
    assert( conf1 == NULL );
    assert( conf2 == NULL );
    assert( c1 );
    assert( c2 );
    conf1 = c1;
    conf2 = c2;
    conf  = r;
  }

  inline Enode * getConf( ) const { return conf; }

  inline void clear     ( )
  {
    while( !cnodes.empty( ) )
    {
      assert( cnodes.back( ) );
      delete cnodes.back( );
      cnodes.pop_back( );
    }
    while ( !cedges.empty( ) )
    {
      assert( cedges.back( ) );
      delete cedges.back( );
      cedges.pop_back( );
    }
    colored = false;
    conf1 = NULL;
    conf2 = NULL;
    conf = NULL;
    cnodes_store.clear( );
  }

private:

  void       color          ( const ipartitions_t & );
  void       colorNodes     ( const ipartitions_t & );
  icolor_t   colorNodesRec  ( CNode *, const ipartitions_t & );
  bool       colorEdges     ( CNode *, CNode *, const ipartitions_t & );
  bool       colorEdgesRec  ( CNode *, CNode *, const ipartitions_t & );
  bool       colorEdgesFrom ( CNode *, const ipartitions_t & );
  void       colorReset     ( );

  bool          getSubpaths          ( const path_t &, path_t &, path_t &, path_t & );
  size_t        getSortedEdges       ( CNode *, CNode *, vector< CEdge * > & );
  Enode *       I                    ( const path_t & );
  Enode *       Irec                 ( const path_t &, map< path_t, Enode * > & );
  Enode *       J                    ( const path_t &, vector< path_t > & );
  void          B                    ( const path_t &, vector< path_t > & );
  void          Brec                 ( const path_t &, vector< path_t > &, set< path_t > & );
  bool          getFactorsAndParents ( const path_t &, vector< path_t > &, vector< path_t > & );
  inline path_t path                 ( CNode * c1, CNode * c2 ) { return make_pair( c1, c2 ); }

  bool          checkColors          ( );

  Enode *       maximize             ( Enode * );

  Egraph &                        egraph;
  SMTConfig &                     config;
  vector< CNode * >               cnodes;
  vector< CEdge * >               cedges;
  map< enodeid_t, CNode * >       cnodes_store;
  set< pair< Enode *, Enode * > > path_seen;
  set< CNode * >                  colored_nodes;
  set< CEdge * >                  colored_edges;
  bool                            colored;
  Enode *                         conf1;
  Enode *                         conf2;
  Enode *                         conf;

  struct CAdjust
  {

    CAdjust( CNode * cnn_, CNode * x_, CNode * n_, CEdge * p_ )
      : cnn( cnn_ ), x( x_ ), n( n_ ), prev( p_ )
    { 
      // Check some preconditions
      assert( prev->source == x );
      assert( prev->target == n );
      assert( x->next );
      assert( x->next == prev );
    }

    // Undo
    inline void undo( )
    {
      // Check some preconditions
      assert( prev->source == x );
      assert( prev->target == n );
      assert( x->next );
      assert( x->next->target == cnn );
      assert( cnn->next );
      assert( cnn->next->target == n );
      assert( x->next != prev );
      assert( cnn->next != prev );
      x->next = prev;
      cnn->next = NULL;
    }

  private:

    CNode * cnn;
    CNode * x;
    CNode * n;
    CEdge * prev;
  };

  vector< CAdjust * > undo_adjust;
};

#endif

#endif
