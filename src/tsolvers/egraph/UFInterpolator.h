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

#include "Logic.h"
#include "SMTConfig.h"
#include "Pterm.h"
#include "TheoryInterpolator.h"

struct CEdge;

struct CNode
{
  CNode( PTRef   e_ )
    :
    e     ( e_ )
    , color ( I_UNDEF )
    , next  ( NULL )
  {
  }

  PTRef   e;
  icolor_t color;
  CEdge *   next;
};

typedef pair< CNode *, CNode * > path_t;

struct CEdge
{
  CEdge ( CNode * s
        , CNode * t
        , PTRef r )
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
  PTRef reason;
  icolor_t color;

  inline friend ostream & operator<<( ostream & os, CEdge * ce )
  {
    //FIXME
    return os;
    //return os << logic.getPterm(ce->source->e) << " ---> " << logic.getPterm(ce->target->e);
  }
};

class Egraph;

class CGraph : public TheoryInterpolator
{
public:

  CGraph( Egraph & egraph_
        , SMTConfig & config_
        , Logic & logic_)
    : egraph  ( egraph_ )
    , config  ( config_ )
    , logic   ( logic_ )
    , colored ( false )
    , conf1   ( PTRef_Undef )
    , conf2   ( PTRef_Undef )
    , conf    ( PTRef_Undef )
    , interpolant (PTRef_Undef)
    , conf_color (I_UNDEF)
    , max_width(0)
    , max_height(0)
    , flat(false)
    , divided(false)
  { }

  ~CGraph( ) { clear( ); }

	inline int     verbose                       ( ) const { return config.verbosity(); }
    void verifyInterpolantWithExternalTool( const ipartitions_t& mask );
  void     addCNode      ( PTRef );
  void     addCEdge      ( PTRef, PTRef, PTRef );
  void     revertEdges   ( CNode * );
  PTRef  getInterpolant( const ipartitions_t & );
  void     printAsDotty  ( ostream & );

  inline void setConf( PTRef c1, PTRef c2, PTRef r )
  {
//      cout << "SetConf: " << logic.printTerm(c1) << " = " << logic.printTerm(c2) << endl;
    assert( conf1 == PTRef_Undef );
    assert( conf2 == PTRef_Undef );
    assert( c1 != PTRef_Undef);
    assert( c2 != PTRef_Undef);
    conf1 = c1;
    conf2 = c2;
    conf  = r;
  }

  inline PTRef getConf( ) const { return conf; }

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
    conf1 = PTRef_Undef;
    conf2 = PTRef_Undef;
    conf = PTRef_Undef;
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

  bool usingStrong() { return config.itp_euf_alg() == 0; }
  bool usingWeak() { return config.itp_euf_alg() == 2; }
  bool usingRandom() { return config.itp_euf_alg() == 3; }

  bool          getSubpaths          ( const path_t &, path_t &, path_t &, path_t & );
  bool          getSubpathsSwap          ( const path_t &, path_t &, path_t &, path_t & );
  size_t        getSortedEdges       ( CNode *, CNode *, vector< CEdge * > & );
  PTRef       I                    ( const path_t & );
  PTRef       Iprime                    ( const path_t & );
  PTRef       ISwap                    ( const path_t & );
  PTRef       IprimeSwap                    ( const path_t & );
  PTRef       Irec                 ( const path_t &, map< path_t, PTRef > & , unsigned int h = 0);
  PTRef       IrecSwap                 ( const path_t &, map< path_t, PTRef > & , unsigned int h = 0);
  PTRef       J                    ( const path_t &, vector< path_t > & );
  PTRef       JSwap                    ( const path_t &, vector< path_t > & );
  void          B                    ( const path_t &, vector< path_t > & );
  void          BSwap                    ( const path_t &, vector< path_t > & );
  void          Brec                 ( const path_t &, vector< path_t > &, set< path_t > & );
  void          BrecSwap                 ( const path_t &, vector< path_t > &, set< path_t > & );
  bool          getFactorsAndParents ( const path_t &, vector< path_t > &, vector< path_t > & );
  void labelFactors( vector<path_t> & );
  PTRef interpolate_flat(const path_t& p);
  bool flat;
  bool divided;
  inline path_t path                 ( CNode * c1, CNode * c2 ) { return make_pair( c1, c2 ); }

  bool          checkColors          ( );

  PTRef       maximize             ( PTRef );

  Egraph &                        egraph;
  SMTConfig &                     config;
  Logic &                         logic;
  vector< CNode * >               cnodes;
  vector< CEdge * >               cedges;
  map< PTRef, CNode * >       cnodes_store;
  set< pair< PTRef, PTRef > > path_seen;
  set< CNode * >                  colored_nodes;
  set< CEdge * >                  colored_edges;
  bool                            colored;
  PTRef                         conf1;
  PTRef                         conf2;
  PTRef                         conf;
  map< path_t, icolor_t > L;
  PTRef interpolant;
  icolor_t conf_color;
  vec<PTRef> A_basic;
  vec<PTRef> B_basic;
  unsigned int max_width;
  unsigned int max_height;

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
