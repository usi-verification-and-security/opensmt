#include "LIASolver.h"
#include "LASolver.h"
#include "lrasolver/LRASolver.h"


static SolverDescr descr_lra_solver("LRA Solver", "Solver for Quantifier Free Linear Real Arithmetics");


bool  LIASolver:: check  ( bool complete) {
    bool rval = LRASolver::check_simplex(complete);
    if (rval == true)
        return checkIntegersAndSplit( );
    return rval;
}

bool LIASolver::isModelInteger(LVRef v) const
{
    return !( model.read(v).hasDelta() || !model.read(v).R().isInteger() );
}

opensmt::Integer2 LIASolver::getInt(PTRef r) {
    return logic.getNumConst(r);
}

LIASolver::~LIASolver( )
{
    lasolverstats.printStatistics(cerr);
    // Remove numbers
//    while( !numbers_pool.empty( ) )
//    {
//        assert( numbers_pool.back( ) );
//        delete numbers_pool.back( );
//        numbers_pool.pop_back( );
//    }
}

/*
//Here starts implementation of LIA solver

bool LIASolver::checkIntegersAndSplit( )
{
  //assert(false);


  //assert( config.lra_integer_solver );
  //assert( removed_by_GaussianElimination.empty( ) );

    for (int i = 0; i < columns.size(); i++) {
        LVRef x = columns[i];
        if (!isModelInteger(x)) {





 // VectorLAVar::const_iterator it = columns.begin( );
  //LAVar * x;

  //  unsigned equality_counter=0;
  //  for( ; it != columns.end( ); ++it )
  //    if (( *it )->isEquality())
  //      equality_counter++;
  //
  //  cout << "Equalities in the complete integer check: " << equality_counter << " out of " << columns.size();

  //it = columns.begin( );

//  for( ; it != columns.end( ); ++it )
//  {
//    assert( !( *it )->skip );
//    if( !( *it )->isModelInteger( ) )
//    {
      //x = *it;

     //  Prepare the variable to store a splitting value
//      Real * c = NULL;
//
//
//      if( !numbers_pool.empty( ) )
//      {
//        c = numbers_pool.back( );
//        numbers_pool.pop_back( );
//      }
//      else
//      {
//        c = new Real( 0 );
//      }

      // Compute a splitting value
//      if( x->M( ).R( ).get_den( ) != 1 )
//      {
//        if( x->M( ).R( ).get_num( ) < 0 )
//          *c = x->M( ).R( ).get_num( ) / x->M( ).R( ).get_den( ) - 1;
//        else
//          *c = x->M( ).R( ).get_num( ) / x->M( ).R( ).get_den( );
//      }
//      else
//      {
//        if( x->M( ).D( ) < 0 )
//          *c = x->M( ).R( ) - 1;
//        else
//          *c = x->M( ).R( );
//      }

      // Check if integer splitting is possible for the current variable
      if( *c < x->L( ) && *c + 1 > x->U( ) )
      {
        vec<PTRef> tmp;
        getConflictingBounds( x, tmp);
        for (int i = 0; i < tmp.size; i++) {
            explanation.push(PtAsgn(tmp[i], getPolarity(tmp[i])));
        }
        for( unsigned i = 0; i < columns.size( ); ++i )
          if( !columns[i]->skip )
            columns[i]->restoreModel( );
        return setStatus( UNSAT );
      }

      vector<Enode *> splitting;

      // Prepare left branch
      Enode * or1 = egraph.mkLeq( egraph.cons( x->e, egraph.cons( egraph.mkNum( *c ) ) ) );
      LAExpression a( or1 );
      or1 = a.toEnode( egraph );
      egraph.inform( or1 );
      splitting.push_back( or1 );

      // Prepare right branch
      Enode * or2 = egraph.mkGeq( egraph.cons( x->e, egraph.cons( egraph.mkNum( *c + 1 ) ) ) );
      LAExpression b( or2 );
      or2 = b.toEnode( egraph );
      egraph.inform( or2 );
      splitting.push_back( or2 );

      //      cout << or1 <<endl;
      //      cout << or2 <<endl;
      // Push splitting clause
      egraph.splitOnDemand( splitting, id );

      // We don't need splitting value anymore
      numbers_pool.push_back( c );

      // We are lazy: save the model and return on the first splitting
      LAVar::saveModelGlobal( );
      checks_history.push_back( pushed_constraints.size( ) );
      return setStatus( SAT );
    }
  }
  // Cool! The model is already integer!
  LAVar::saveModelGlobal( );
  checks_history.push_back( pushed_constraints.size( ) );
  return setStatus( SAT );

    //return false;
}
}
}

// end of LIA solver implementation

*/