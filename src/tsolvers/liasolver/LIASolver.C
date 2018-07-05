#include "LIASolver.h"
#include "LASolver.h"
#include "lrasolver/LRASolver.h"


static SolverDescr descr_lra_solver("LRA Solver", "Solver for Quantifier Free Linear Real Arithmetics");


bool  LIASolver:: check  ( bool complete) {
    bool rval = check_simplex(complete);
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

void LIASolver::computeConcreteModel(LVRef v) {
    while (concrete_model.size() <= lva[v].ID())
        concrete_model.push(nullptr);

    PTRef tr = lva[v].getPTRef();
    auto it = removed_by_GaussianElimination.find(v);
    if(it != removed_by_GaussianElimination.end()){
        auto const & representation = (*it).second;
        Delta val;
        for (auto const & term : representation) {
            val += term.second * model.read(term.first);
        }
        concrete_model[lva[v].ID()] = new opensmt::Real(val.R());
    }
    else {
        concrete_model[lva[v].ID()] = new opensmt::Real(model.read(v).R());
    }
}


//
// Detect the appropriate value for symbolic delta and stores the model
//

void LIASolver::computeModel()
{
    assert( status == SAT );
/*
    Real minDelta(0);
    Real maxDelta(0);
    Delta curDelta(0);
    Delta curBound(Delta::ZERO);
*/
    Delta delta_abst = Delta_PlusInf;  // We support plus infinity for this one.

    // Let x be a LV variable such that there are asserted bounds c_1 <= x and x <= c_2, where
    // (1) c_1 = (i1 | s1), c_2 = (i2 | -s2)
    // (2) s1, s2 \in {0, 1}
    // (3) val(x) = (R | D).
    // Then delta(x) := (i1+i2)/2 - R.
    // If x is not bounded from below or above, i.e., c_1 <= x, or x <= c_2, or neither, then
    // delta(x) := + Infty.
    // Now D at the same time is equal to k*\delta', and we need a value for \delta'.  So
    // \delta'(x) = D/k
    // Finally, \delta := min_{x \in LV |delta'(x)|}.

    for (unsigned i = 0; i < lavarStore.numVars(); ++i)
    {
        LVRef v = lavarStore.getVarByIdx(i);
        assert (model.read(v).D() == 0);

    }

#ifdef GAUSSIAN_DEBUG
    cerr << "; delta: " << curDelta << '\n';
#endif

    for ( unsigned i = 0; i < lavarStore.numVars(); i++)
    {
        LVRef v = lavarStore.getVarByIdx(i);
        computeConcreteModel(v);
    }
//    // Compute the value for each variable. Delta is taken into account
//    for ( unsigned i = 0; i < columns.size( ); ++i )
//        computeConcreteModel(columns[i], curDelta);
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