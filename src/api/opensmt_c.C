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

#include "opensmt_c.h"
#include "OpenSMTContext.h"
#include "Egraph.h"
#include "Tseitin.h"
#include "SimpSMTSolver.h"

#ifndef SMTCOMP

#define CAST( FROM, TO ) \
  assert( FROM ); \
  OpenSMTContext * FROM_ = static_cast< OpenSMTContext * >( FROM ); \
  OpenSMTContext & TO = *FROM_;

//
// Communication APIs
//
void opensmt_set_verbosity( opensmt_context, int )
{
  // assert( c );
  // OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  // OpenSMTContext & context = *c_;
}

char * opensmt_version( )
{
  return const_cast< char * >( PACKAGE_STRING );
}

opensmt_context opensmt_mk_context( opensmt_logic l )
{
  OpenSMTContext * c = new OpenSMTContext( );
  OpenSMTContext & context = *c;
  // IMPORTANT: 
  // Any parameter in the config should be set
  // here, BEFORE SetLogic is called. In SetLogic
  // solvers are initialized with values taken
  // from the config ...
  SMTConfig & config = context.getConfig( );
  // When API is active incremental solving must be on
  config.incremental = 1;
  //
  // Set ad-hoc default parameters
  //
  if ( l == qf_ct )
  {
    // Settings copied/adapted from pbct 0.1.2
    config.sat_polarity_mode = 1;   
    config.sat_use_luby_restart = 1;
    config.sat_preprocess_booleans = 0;
    config.uf_disable = 1;
  }
  // Set the right logic
  switch( l )
  {
    case qf_uf:    context.SetLogic( QF_UF );    break;
    case qf_bv:    context.SetLogic( QF_BV );    break;
    case qf_rdl:   context.SetLogic( QF_RDL );   break;
    case qf_idl:   context.SetLogic( QF_IDL );   break;
    case qf_lra:   context.SetLogic( QF_LRA );   break;
    case qf_lia:   context.SetLogic( QF_LIA );   break;
    case qf_ufidl: context.SetLogic( QF_UFIDL ); break;
    case qf_uflra: context.SetLogic( QF_UFLRA ); break;
    case qf_bool:  context.SetLogic( QF_BOOL );  break;
    case qf_ct:    context.SetLogic( QF_CT );    break;
    opensmt_error2( "unsupported logic: ", l );
  }

  // Return context
  return static_cast< void * >( c );
}

void opensmt_del_context( opensmt_context c )
{
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  delete c_;
}

void opensmt_reset( opensmt_context c )
{
  CAST( c, context );
  context.Reset( );
}

void opensmt_dump_assertions_to_file( opensmt_context c, const char * file )
{
  CAST( c, context );
  context.DumpAssertionsToFile( file );
}

void opensmt_print_expr( opensmt_expr e )
{
  Enode * enode = static_cast< Enode * >( e );
  cerr << enode;
}

void opensmt_push( opensmt_context c )
{
  CAST( c, context );
  context.Push( );
}

void opensmt_pop( opensmt_context c )
{
  CAST( c, context );
  context.Pop( );
}

void opensmt_assert( opensmt_context c, opensmt_expr e )
{
  assert( e );
  CAST( c, context );
  Enode * expr = static_cast< Enode * >( e );
  context.Assert( expr );
}

opensmt_result opensmt_check( opensmt_context c )
{
  CAST( c, context );
  lbool result = context.CheckSAT( );
  if ( result == l_Undef ) return l_undef;
  if ( result == l_False ) return l_false;
  return l_true;
}

opensmt_result opensmt_check_assump( opensmt_context c, opensmt_expr l )
{
  CAST( c, context );
  Enode * unit = static_cast< Enode * >( l );
  assert( unit );
  vec< Enode * > assumptions;
  assumptions.push( unit );
  lbool result = context.CheckSAT( assumptions );
  if ( result == l_Undef ) return l_undef;
  if ( result == l_False ) return l_false;
  assert( result == l_True );
  return l_true;
}

opensmt_result opensmt_check_lim_assump( opensmt_context c
                                       , opensmt_expr l
				       , unsigned limit )
{
  CAST( c, context );
  Enode * unit = static_cast< Enode * >( l );
  assert( unit );
  vec< Enode * > assumptions;
  assumptions.push( unit );
  lbool result = context.CheckSAT( assumptions, limit );
  if ( result == l_Undef ) return l_undef;
  if ( result == l_False ) return l_false;
  return l_true;
}

//
// Model APIs
//
void opensmt_print_model( opensmt_context c, const char * filename )
{
  CAST( c, context );
  ofstream os( filename );
  context.PrintModel( os );
}

#if 0
//
// Proof/Interpolation APIs
//
void opensmt_print_proof( opensmt_context
#ifdef PRODUCE_PROOF
    c
#endif
    , const char *
#ifdef PRODUCE_PROOF
    filename
#endif
    )
{
#ifdef PRODUCE_PROOF
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  ofstream os( filename );
  context.printProof( os );
#else
  error( "you should compile with PRODUCE_PROOF flag enabled (--enable-proof flag in configure)", "" );
#endif
}

void opensmt_print_interpolant( opensmt_context
#ifdef PRODUCE_PROOF
    c
#endif
    , const char *
#ifdef PRODUCE_PROOF
    filename
#endif
    )
{
#ifdef PRODUCE_PROOF
  assert( c );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  ofstream os( filename );
  context.printInter( os );
#else
  error( "you should compile with PRODUCE_PROOF flag enabled (--enable-proof flag in configure)", "" );
#endif
}
#endif

//
// Formula construction APIs
//
opensmt_expr opensmt_mk_true( opensmt_context c )
{
  CAST( c, context );
  Enode * res = context.mkTrue( );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_false( opensmt_context c )
{
  CAST( c, context );
  Enode * res = context.mkFalse( );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bool_var( opensmt_context c, char * s )
{
  assert( s );
  CAST( c, context );
  Snode * sort = context.mkSortBool( );
  context.DeclareFun( s, NULL, sort );
  Enode * res = context.mkVar( s, true );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_int_var( opensmt_context c, char * s )
{
  assert( s );
  CAST( c, context );
  Snode * sort = context.mkSortInt( );
  context.DeclareFun( s, NULL, sort );
  Enode * res = context.mkVar( s, true );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_real_var( opensmt_context c, char * s )
{
  assert( s );
  CAST( c, context );
  Snode * sort = context.mkSortReal( );
  context.DeclareFun( s, NULL, sort );
  Enode * res = context.mkVar( s, true );
  return static_cast< void * >( res );
}

/*
opensmt_expr opensmt_mk_bv_var( opensmt_context c, char * s, unsigned w )
{
  assert( c );
  assert( s );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * res = context.mkVar( s, true );
  return static_cast< void * >( res );
}
*/

opensmt_expr opensmt_mk_cost_var( opensmt_context c, char * s )
{
  assert( s );
  CAST( c, context );
  Snode * sort = context.mkSortCost( );
  context.DeclareFun( s, NULL, sort );
  Enode * res = context.mkVar( s, true );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_or( opensmt_context c, opensmt_expr * expr_list, unsigned n )
{
  CAST( c, context );
  assert( expr_list );
  list< Enode * > args;
  for ( unsigned i = 0 ; i < n ; i ++ )
  {
    Enode * arg = static_cast< Enode * >( expr_list[ i ] );
    args.push_back( arg );
  }
  Enode * args_list = context.mkCons( args );
  Enode * res = context.mkOr( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_and( opensmt_context c, opensmt_expr * expr_list, unsigned n )
{
  CAST( c, context );
  assert( expr_list );
  list< Enode * > args;
  for ( unsigned i = 0 ; i < n ; i ++ )
  {
    Enode * arg = static_cast< Enode * >( expr_list[ i ] );
    args.push_back( arg );
  }
  Enode * args_list = context.mkCons( args );
  Enode * res = context.mkAnd( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_eq ( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  CAST( c, context );
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkEq( args_list );
  return static_cast< void * >( res );
 }

opensmt_expr opensmt_mk_ite( opensmt_context c, opensmt_expr i, opensmt_expr t, opensmt_expr e )
{
  CAST( c, context );
  Enode * i_ = static_cast< Enode * >( i );
  Enode * t_ = static_cast< Enode * >( t );
  Enode * e_ = static_cast< Enode * >( e );
  Enode * args = context.mkCons( i_
               , context.mkCons( t_
	       , context.mkCons( e_ ) ) );
  Enode * res = context.mkIte( args );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_not( opensmt_context c, opensmt_expr x)
{
  CAST( c, context );
  Enode * args_list = context.mkCons( static_cast< Enode * >( x ));
  Enode * res = context.mkNot( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_num_from_string( opensmt_context c, const char * s )
{
  CAST( c, context );
  assert( s );
  Enode * res = context.mkNum( s );
  return res;
}

opensmt_expr opensmt_mk_num_from_mpz( opensmt_context c, const mpz_t n )
{
  assert( n );
  CAST( c, context );
  mpz_class n_( n );
  Real num( n_ );
  Enode * res = context.mkNum( num );
  return res;
}

opensmt_expr opensmt_mk_num_from_mpq( opensmt_context c, const mpq_t n )
{
  assert( n );
  CAST( c, context );
  mpq_class n_( n );
  Real num( n_ );
  Enode * res = context.mkNum( num );
  return res;
}

opensmt_expr opensmt_mk_plus( opensmt_context c, opensmt_expr * expr_list, unsigned n )
{
  CAST( c, context );
  list< Enode * > args;
  for ( unsigned i = 0 ; i < n ; i ++ )
  {
    Enode * arg = static_cast< Enode * >( expr_list[ i ] );
    args.push_back( arg );
  }
  Enode * args_list = context.mkCons( args );
  Enode * res = context.mkPlus( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_minus( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  CAST( c, context );
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkMinus( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_times( opensmt_context c, opensmt_expr * expr_list, unsigned n )
{
  CAST( c, context );
  list< Enode * > args;
  for ( unsigned i = 0 ; i < n ; i ++ )
  {
    Enode * arg = static_cast< Enode * >( expr_list[ i ] );
    args.push_back( arg );
  }
  Enode * args_list = context.mkCons( args );
  Enode * res = context.mkTimes( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_leq( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  CAST( c, context );
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkLeq( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_lt( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  CAST( c, context );
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkLt( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_gt( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  CAST( c, context );
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkGt( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_geq( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  CAST( c, context );
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkGeq( args_list );
  return static_cast< void * >( res );
}

/*
opensmt_expr opensmt_mk_bv_constant( opensmt_context c, unsigned w, unsigned long n )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  char buf[ 1024 ];
  sprintf( buf, "bv%ld[%d]", n, w );
  Enode * res = context.mkBvnum( buf );
  return res;
}

opensmt_expr opensmt_mk_bv_constant_from_string( opensmt_context c, unsigned w, const char * s )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  char buf[ 1024 ];
  sprintf( buf, "bv%s[%d]", s, w );
  Enode * res = context.mkBvnum( buf );
  return res;
}

opensmt_expr opensmt_mk_bv_add( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvadd( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_sub( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvsub( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_mul( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvmul( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_neg( opensmt_context c, opensmt_expr x )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x ) );
  Enode * res = context.mkBvneg( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_concat( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkConcat( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_and( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvand( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_or( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvor( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_xor( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvxor( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_not( opensmt_context c, opensmt_expr x )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x ) );
  Enode * res = context.mkBvnot( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_extract( opensmt_context c, unsigned msb, unsigned lsb, opensmt_expr x )
{
  assert( c );
  assert( x );
  assert( lsb <= msb );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * arg = static_cast< Enode * >( x );
  Enode * res = context.mkExtract( msb, lsb, arg );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_sign_extend( opensmt_context c, opensmt_expr x, unsigned n )
{
  assert( c );
  assert( x );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * arg = static_cast< Enode * >( x );
  Enode * res = context.mkSignExtend( n, arg );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_zero_extend( opensmt_context c, opensmt_expr x, unsigned n )
{
  assert( c );
  assert( x );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * arg = static_cast< Enode * >( x );
  Enode * res = context.mkZeroExtend( n, arg );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_shift_left( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  assert( c );
  assert( x );
  assert( y );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvshl( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_shift_right( opensmt_context c, opensmt_expr x, opensmt_expr y )
{
  assert( c );
  assert( x );
  assert( y );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvlshr( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_lt( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvult( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_le( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvule( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_gt( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvugt( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_ge( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvuge( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_slt( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvslt( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_sle( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvsle( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_sgt( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvsgt( args_list );
  return static_cast< void * >( res );
}

opensmt_expr opensmt_mk_bv_sge( opensmt_context c, opensmt_expr lhs, opensmt_expr rhs )
{
  assert( c );
  assert( lhs );
  assert( rhs );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( lhs )
                    , context.mkCons( static_cast< Enode * >( rhs ) ) );
  Enode * res = context.mkBvsge( args_list );
  return static_cast< void * >( res );
}
*/

opensmt_expr opensmt_mk_ct_incur( opensmt_context c
                                , opensmt_expr    var
				, opensmt_expr    cost
				, opensmt_expr    id )
{
  CAST( c, context );

  assert( var );
  assert( cost );
  assert( id );

  Enode * evar  = static_cast< Enode * >( var );
  Enode * ecost = static_cast< Enode * >( cost );
  Enode * eid   = static_cast< Enode * >( id );
  Enode * args = context.mkCons( evar
	       , context.mkCons( ecost
	       , context.mkCons( eid ) ) );
  Enode * result = context.mkCostIncur( args );
  return static_cast< void * >( result );
}

opensmt_expr opensmt_mk_ct_bound( opensmt_context c
                                , opensmt_expr    var
				, opensmt_expr    cost )
{
  CAST( c, context );

  assert( var );
  assert( cost );

  Enode * evar  = static_cast< Enode * >( var );
  Enode * ecost = static_cast< Enode * >( cost );
  Enode * args = context.mkCons( evar,
                 context.mkCons( ecost ) );
  Enode * result = context.mkCostBound( args );
  return static_cast< void * >( result );
}

unsigned opensmt_conflicts( opensmt_context c )
{
  CAST( c, context );
  return context.getLearnts( );
}

unsigned opensmt_decisions( opensmt_context c )
{
  CAST( c, context );
  return context.getDecisions( );
}

opensmt_expr opensmt_get_value( opensmt_context c, opensmt_expr v )
{
  assert( v );
  CAST( c, context );
  assert( context.getStatus( ) == l_True );
  Enode * var = static_cast< Enode * >( v );
  const Real & value = var->getValue();
  Enode * res = context.mkNum( value );
  return static_cast< void * >( res );
}

void opensmt_get_num( opensmt_expr n, mpz_t val )
{
  assert( n );
  Enode * num = static_cast< Enode * >( n );
  assert( num->isConstant() );
  Real r = num->getValue();
  mpz_set( val, r.get_num().get_mpz_t() );
}

opensmt_result opensmt_get_bool( opensmt_context c, opensmt_expr p )
{
  assert( p );
  CAST( c, context );
  Enode * atom = static_cast< Enode * >( p );
  lbool value = context.getModel( atom );
  if ( value == l_True )
  {
    return l_true;
  }
  else if ( value == l_False )
  {
    return l_false;
  }
  return l_undef;
}

void opensmt_polarity( opensmt_context, opensmt_expr, int )
{
  // assert( c );
  // assert( a );
  // bool positive = static_cast< bool >( pos );
  // OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  // OpenSMTContext & context = *c_;
  // SimpSMTSolver & solver = context.solver;
  // Enode * atom = static_cast< Enode * >( a );
}

#endif
