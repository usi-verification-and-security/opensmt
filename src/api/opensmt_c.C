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

#include "opensmt_c.h"
#include "MainSolver.h"
#include "SimpSMTSolver.h"
//#include "OpenSMTContext.h"
//#include "Egraph.h"
//#include "Tseitin.h"

#ifndef SMTCOMP

#define CAST( CONTEXT, SOLVER ) \
  assert( CONTEXT.c ); \
  MainSolver * SOLVER_ = static_cast< MainSolver * >( CONTEXT.c ); \
  SOLVER = SOLVER_;

#define CAST_E( EXPR, PTREF ) \
  PTRef PTREF_ = { EXPR.x }; \
  PTREF = PTREF_;
//#define CAST( FROM, TO ) \
//  assert( FROM ); \
//  OpenSMTContext * FROM_ = static_cast< OpenSMTContext * >( FROM ); \
//  OpenSMTContext & TO = *FROM_;

//
// Communication APIs
//
void osmt_set_verbosity( osmt_context c, int i)
{
    assert(c.c);
    MainSolver* solver;
    CAST(c, solver);
    const char* msg;
    solver->getConfig().setOption("verbosity", i, msg);
}

char * osmt_version( )
{
  return const_cast< char * >( PACKAGE_STRING );
}

osmt_context osmt_mk_context( osmt_logic l )
{
    SMTConfig *config = new SMTConfig();
    if (l == qf_uf)
    {
        UFTheory *uftheory = new UFTheory(*config);
        THandler *thandler = new THandler(*config, *uftheory);
        SimpSMTSolver* solver = new SimpSMTSolver(*config, *thandler);
        MainSolver* mainSolver = new MainSolver(*thandler, *config, solver);
        // Return MainSolver
        return { mainSolver };
    }
    else {
        opensmt_error2( "unsupported logic: ", l );
        return { NULL };
    }
}

void osmt_del_context( osmt_context c )
{
    assert( c.c );
    MainSolver* solver;
    CAST(c, solver);
    delete solver;
}

void osmt_reset( osmt_context c )
{
//    CAST( c, context );
//    context.Reset( );
}

void osmt_dump_assertions_to_file( osmt_context c, const char * file )
{
//    CAST( c, context );
//    context.DumpAssertionsToFile( file );
}

void osmt_print_expr( osmt_context c, osmt_expr e )
{
    MainSolver* solver;
    CAST(c, solver);
    PTRef tr = { e.x };
    cerr << solver->getLogic().printTerm(tr);
}

void osmt_push(osmt_context c, osmt_expr e)
{
    MainSolver* solver;
    CAST(c, solver);
    PTRef tr = { e.x };
    solver->push(tr);
}

void osmt_pop(osmt_context)
{
//    CAST( c, context );
//    context.Pop( );
}


osmt_result osmt_check( osmt_context c )
{
    MainSolver* solver;
    CAST(c, solver);
    sstat result = solver->check();
    if (result == s_True) return l_true;
    if (result == s_False) return l_false;
    return l_undef;
}

//
// Model APIs
//
void osmt_get_model( osmt_context c, const char * filename )
{
    MainSolver* solver;
    CAST(c, solver);
    ofstream os(filename);
//    solver->PrintModel(os);
}

#if 0
//
// Proof/Interpolation APIs
//
void osmt_print_proof( osmt_context
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

void osmt_print_interpolant( osmt_context
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
osmt_expr osmt_mk_true( osmt_context c )
{
    MainSolver* solver;
    CAST(c, solver);
    PTRef tr = solver->getLogic().getTerm_true();
    return { tr.x } ;
}

osmt_expr osmt_mk_false( osmt_context c )
{
    MainSolver* solver;
    CAST(c, solver);
    PTRef tr = solver->getLogic().getTerm_false( );
    return { tr.x };
}

osmt_expr osmt_mk_bool_var(osmt_context c, const char * s)
{
    assert( s );
    MainSolver* solver;
    CAST( c, solver);
    PTRef tr = solver->getLogic().mkBoolVar(s);
    return { tr.x };
}

osmt_expr osmt_mk_int_var(osmt_context c, const char * s)
{
//    assert( s );
//    CAST( c, context );
//    Snode * sort = context.mkSortInt( );
//    context.DeclareFun( s, NULL, sort );
//    Enode * res = context.mkVar( s, true );
//    return static_cast< void * >( res );
}

osmt_expr osmt_mk_real_var( osmt_context c, const char * s )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(solver->getLogic().getLogic() == QF_LRA);
    assert(s);
    PTRef tr = static_cast<LRALogic&>(solver->getLogic()).mkRealVar(s);
    return { tr.x };
}

//osmt_expr osmt_mk_bv_var( osmt_context c, const char * s, unsigned w )
//{
//  assert( c );
//  assert( s );
//  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
//  OpenSMTContext & context = *c_;
//  Enode * res = context.mkVar( s, true );
//  return static_cast< void * >( res );
//}

//osmt_expr osmt_mk_cost_var( osmt_context c, const char * s )
//{
//  assert( s );
//  CAST( c, context );
//  Snode * sort = context.mkSortCost( );
//  context.DeclareFun( s, NULL, sort );
//  Enode * res = context.mkVar( s, true );
//  return static_cast< void * >( res );
//}

osmt_expr osmt_mk_or( osmt_context c, osmt_expr * expr_list, unsigned n )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(expr_list);
    vec<PTRef> args;
    for (unsigned i = 0 ; i < n ; i ++)
    {
        PTRef arg = { expr_list[i].x };
        args.push(arg);
    }
    PTRef res = solver->getLogic().mkOr(args);
    return { res.x };
}

osmt_expr osmt_mk_and( osmt_context c, osmt_expr * expr_list, unsigned n )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(expr_list);
    vec<PTRef> args;
    for (unsigned i = 0 ; i < n ; i ++)
    {
        PTRef arg = { expr_list[i].x };
        args.push(arg);
    }
    PTRef res = solver->getLogic().mkAnd(args);
    return { res.x };
}

osmt_expr osmt_mk_eq(osmt_context c, osmt_expr x, osmt_expr y)
{
    MainSolver* solver;
    CAST(c, solver);
    PTRef res = solver->getLogic().mkEq({x.x}, {y.x});
    return { res.x };
 }

osmt_expr osmt_mk_ite( osmt_context c, osmt_expr i, osmt_expr t, osmt_expr e )
{
    MainSolver* solver;
    CAST(c, solver);
    PTRef res = solver->getLogic().mkIte({i.x}, {t.x}, {e.x});
    return { res.x };
}

osmt_expr osmt_mk_not( osmt_context c, osmt_expr x)
{
    MainSolver* solver;
    CAST(c, solver);
    PTRef res = solver->getLogic().mkNot({x.x});
    return { res.x };
}

osmt_expr osmt_mk_num_from_string( osmt_context c, const char * s )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(solver->getLogic().getLogic() == QF_LRA);
    assert(s);
    PTRef res = static_cast<LRALogic&>(solver->getLogic()).mkConst(s);
    return { res.x };
}

osmt_expr osmt_mk_num_from_frac( osmt_context c, const int nom, const int den )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(solver->getLogic().getLogic() == QF_LRA);
    opensmt::Real num(nom, den);
    PTRef res = static_cast<LRALogic&>(solver->getLogic()).mkConst(num);
    return { res.x };
}

osmt_expr osmt_mk_num_from_num( osmt_context c, const int number )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(solver->getLogic().getLogic() == QF_LRA);
    opensmt::Real num(number);
    PTRef res = static_cast<LRALogic&>(solver->getLogic()).mkConst(num);
    return { res.x };
}

//osmt_expr osmt_mk_num_from_mpq( osmt_context c, const mpq_t n )
//{
//    assert( n );
//    MainSolver* solver;
//    CAST(c, solver);
//    mpq_class n_(n);
//    opensmt::Real num( n_ );
//    PTRef res = static_cast<LRALogic&>(solver->getLogic()).mkConst(num);
//    return res;
//}

osmt_expr osmt_mk_plus( osmt_context c, osmt_expr * expr_list, unsigned n )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(solver->getLogic().getLogic() == QF_LRA);
    vec<PTRef> args;
    for ( unsigned i = 0 ; i < n ; i ++ )
        args.push({expr_list[i].x});

    PTRef res = static_cast<LRALogic&>(solver->getLogic()).mkRealPlus(args);
    return { res.x };
}

osmt_expr osmt_mk_minus( osmt_context c, osmt_expr x, osmt_expr y )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(solver->getLogic().getLogic() == QF_LRA);

    PTRef res = static_cast<LRALogic&>(solver->getLogic()).mkRealMinus({x.x}, {y.x});
    return { res.x };
}

osmt_expr osmt_mk_times( osmt_context c, osmt_expr * expr_list, unsigned n )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(solver->getLogic().getLogic() == QF_LRA);
    vec<PTRef> args;
    for ( unsigned i = 0 ; i < n ; i ++ )
    {
        PTRef arg = { expr_list[i].x };
        args.push(arg);
    }
    PTRef res = static_cast<LRALogic&>(solver->getLogic()).mkRealTimes(args);
    return { res.x };
}

osmt_expr osmt_mk_leq( osmt_context c, osmt_expr lhs, osmt_expr rhs )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(solver->getLogic().getLogic() == QF_LRA);
    PTRef res = static_cast<LRALogic&>(solver->getLogic()).mkRealLeq({lhs.x}, {rhs.x});

    return { res.x };
}

osmt_expr osmt_mk_lt( osmt_context c, osmt_expr lhs, osmt_expr rhs )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(solver->getLogic().getLogic() == QF_LRA);
    PTRef res = static_cast<LRALogic&>(solver->getLogic()).mkRealLt({lhs.x}, {rhs.x});
    return { res.x };
}

osmt_expr osmt_mk_gt( osmt_context c, osmt_expr lhs, osmt_expr rhs )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(solver->getLogic().getLogic() == QF_LRA);
    PTRef res = static_cast<LRALogic&>(solver->getLogic()).mkRealGt({lhs.x}, {rhs.x});
    return { res.x };
}

osmt_expr osmt_mk_geq( osmt_context c, osmt_expr lhs, osmt_expr rhs )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(solver->getLogic().getLogic() == QF_LRA);
    PTRef res = static_cast<LRALogic&>(solver->getLogic()).mkRealGeq({lhs.x}, {rhs.x});
    return { res.x };
}

/*
osmt_expr osmt_mk_bv_constant( osmt_context c, unsigned w, unsigned long n )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  char buf[ 1024 ];
  sprintf( buf, "bv%ld[%d]", n, w );
  Enode * res = context.mkBvnum( buf );
  return res;
}

osmt_expr osmt_mk_bv_constant_from_string( osmt_context c, unsigned w, const char * s )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  char buf[ 1024 ];
  sprintf( buf, "bv%s[%d]", s, w );
  Enode * res = context.mkBvnum( buf );
  return res;
}

osmt_expr osmt_mk_bv_add( osmt_context c, osmt_expr x, osmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvadd( args_list );
  return static_cast< void * >( res );
}

osmt_expr osmt_mk_bv_sub( osmt_context c, osmt_expr x, osmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvsub( args_list );
  return static_cast< void * >( res );
}

osmt_expr osmt_mk_bv_mul( osmt_context c, osmt_expr x, osmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvmul( args_list );
  return static_cast< void * >( res );
}

osmt_expr osmt_mk_bv_neg( osmt_context c, osmt_expr x )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x ) );
  Enode * res = context.mkBvneg( args_list );
  return static_cast< void * >( res );
}

osmt_expr osmt_mk_bv_concat( osmt_context c, osmt_expr x, osmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkConcat( args_list );
  return static_cast< void * >( res );
}

osmt_expr osmt_mk_bv_and( osmt_context c, osmt_expr x, osmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvand( args_list );
  return static_cast< void * >( res );
}

osmt_expr osmt_mk_bv_or( osmt_context c, osmt_expr x, osmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvor( args_list );
  return static_cast< void * >( res );
}

osmt_expr osmt_mk_bv_xor( osmt_context c, osmt_expr x, osmt_expr y )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x )
                    , context.mkCons( static_cast< Enode * >( y ) ) );
  Enode * res = context.mkBvxor( args_list );
  return static_cast< void * >( res );
}

osmt_expr osmt_mk_bv_not( osmt_context c, osmt_expr x )
{
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * args_list = context.mkCons( static_cast< Enode * >( x ) );
  Enode * res = context.mkBvnot( args_list );
  return static_cast< void * >( res );
}

osmt_expr osmt_mk_bv_extract( osmt_context c, unsigned msb, unsigned lsb, osmt_expr x )
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

osmt_expr osmt_mk_bv_sign_extend( osmt_context c, osmt_expr x, unsigned n )
{
  assert( c );
  assert( x );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * arg = static_cast< Enode * >( x );
  Enode * res = context.mkSignExtend( n, arg );
  return static_cast< void * >( res );
}

osmt_expr osmt_mk_bv_zero_extend( osmt_context c, osmt_expr x, unsigned n )
{
  assert( c );
  assert( x );
  OpenSMTContext * c_ = static_cast< OpenSMTContext * >( c );
  OpenSMTContext & context = *c_;
  Enode * arg = static_cast< Enode * >( x );
  Enode * res = context.mkZeroExtend( n, arg );
  return static_cast< void * >( res );
}

osmt_expr osmt_mk_bv_shift_left( osmt_context c, osmt_expr x, osmt_expr y )
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

osmt_expr osmt_mk_bv_shift_right( osmt_context c, osmt_expr x, osmt_expr y )
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

osmt_expr osmt_mk_bv_lt( osmt_context c, osmt_expr lhs, osmt_expr rhs )
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

osmt_expr osmt_mk_bv_le( osmt_context c, osmt_expr lhs, osmt_expr rhs )
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

osmt_expr osmt_mk_bv_gt( osmt_context c, osmt_expr lhs, osmt_expr rhs )
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

osmt_expr osmt_mk_bv_ge( osmt_context c, osmt_expr lhs, osmt_expr rhs )
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

osmt_expr osmt_mk_bv_slt( osmt_context c, osmt_expr lhs, osmt_expr rhs )
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

osmt_expr osmt_mk_bv_sle( osmt_context c, osmt_expr lhs, osmt_expr rhs )
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

osmt_expr osmt_mk_bv_sgt( osmt_context c, osmt_expr lhs, osmt_expr rhs )
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

osmt_expr osmt_mk_bv_sge( osmt_context c, osmt_expr lhs, osmt_expr rhs )
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

//osmt_expr osmt_mk_ct_incur( osmt_context c
//                                , osmt_expr    var
//				, osmt_expr    cost
//				, osmt_expr    id )
//{
//  CAST( c, context );
//
//  assert( var );
//  assert( cost );
//  assert( id );
//
//  Enode * evar  = static_cast< Enode * >( var );
//  Enode * ecost = static_cast< Enode * >( cost );
//  Enode * eid   = static_cast< Enode * >( id );
//  Enode * args = context.mkCons( evar
//	       , context.mkCons( ecost
//	       , context.mkCons( eid ) ) );
//  Enode * result = context.mkCostIncur( args );
//  return static_cast< void * >( result );
//}
//
//osmt_expr osmt_mk_ct_bound( osmt_context c
//                                , osmt_expr    var
//				, osmt_expr    cost )
//{
//  CAST( c, context );
//
//  assert( var );
//  assert( cost );
//
//  Enode * evar  = static_cast< Enode * >( var );
//  Enode * ecost = static_cast< Enode * >( cost );
//  Enode * args = context.mkCons( evar,
//                 context.mkCons( ecost ) );
//  Enode * result = context.mkCostBound( args );
//  return static_cast< void * >( result );
//}

unsigned osmt_conflicts( osmt_context c )
{
    MainSolver* solver;
    CAST(c, solver);
    return solver->getSMTSolver().conflicts;
}

unsigned osmt_decisions( osmt_context c )
{
    MainSolver* solver;
    CAST(c, solver);
    return solver->getSMTSolver().decisions;
}

osmt_expr osmt_get_value( osmt_context c, osmt_expr v )
{
    MainSolver* solver;
    CAST(c, solver);
    assert(solver->getLogic().getLogic() == QF_LRA);
    assert(solver->getStatus() == s_True );
    PTRef tr = { v.x };

    ValPair vp = solver->getValue(tr);
    osmt_expr vpe = osmt_mk_real_var(c, vp.val);
    return vpe;
}

//void osmt_get_num(osmt_context c, osmt_expr n, mpz_t val )
//{
//    MainSolver* solver;
//    CAST(c, solver);
//    assert(solver->getLogic().getLogic() == QF_LRA);
//    assert( n );
//    LRALogic& lralogic = static_cast<LRALogic&>(solver->getLogic());
//    PTRef tr = { n.x };
//    assert(lralogic.isConstant(tr));
//    Real r = lralogic.getRealConst(tr);
//    mpz_set( val, r.get_num().get_mpz_t() );
//}

osmt_result osmt_get_bool( osmt_context c, osmt_expr p )
{
    MainSolver* solver;
    CAST(c, solver);
    PTRef atom = { p.x };
    lbool value = solver->getTermValue(atom);
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

void osmt_polarity( osmt_context, osmt_expr, int )
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
