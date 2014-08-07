/*********************************************************************
 Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
 , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

 OpenSMT -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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

#include "LRASolver.h"
#include "LAVar.h"
#include "Egraph.h"
#include "LA.h"

//#include "../liasolver/LIASolver.h"

//TODO: requires refactoring

//
// Reads the constraint into the solver
//
lbool LRASolver::inform( Enode * e )
{
  if( status != INIT )
  {
    // Treat the Enode as it is pushed on-the-fly
    //    status = INCREMENT;
    assert( status == SAT );
  }
  assert( e->isAtom( ) );
  assert( e->isLeq( ) );

  Enode * arg1 = e->get1st( );
  Enode * arg2 = e->get2nd( );

  bool revert = false;

  if( !( arg1->isConstant( ) ) )
  {
    arg2 = e->get1st( );
    arg1 = e->get2nd( );
    revert = true;
  }

  assert( arg1->isConstant( ) );
  assert( arg2->isTimes( ) || arg2->isPlus( ) );

  // parse the var x of the contraint a < c*x
  if( arg2->isTimes( ) )
  {
    LAVar * x;
    Enode * coef;
    Enode * var;

    // check the value from a
    if( !arg1->isConstant( ) )
      opensmt_error2( "Unexpected number a in  a <= c*x: ", arg1 );

    Real * p_v;
    if( !numbers_pool.empty( ) )
    {
      p_v = numbers_pool.back( );
      numbers_pool.pop_back( );
      *p_v = Real( arg1->getComplexValue( ) );
    }
    else
    {
      p_v = new Real( arg1->getComplexValue( ) );
    }

    coef = arg2->get1st( );
    var = arg2->get2nd( );

    // divide a by the value from c
    const Real& c = coef->getComplexValue( );

    if( coef->isConstant( ) )
      *p_v /= c;
    else
      opensmt_error2( "Unexpected coef c in  a <= c*x : ", coef );

    if( c < 0 )
      revert = !revert;

    assert( config.logic != QF_LRA || var->isVar( ) );
    assert( config.logic != QF_LIA || var->isVar( ) );
    assert( config.logic != QF_UFLRA || var->isVar( ) || var->isUf( ) );

    // check if we need a new LAVar for a given var
    if( var->getId( ) >= ( int )enode_lavar.size( ) )
      enode_lavar.resize( var->getId( ) + 1, NULL );

    if( enode_lavar[var->getId( )] == NULL )
    {
      assert( status == INIT );

      x = new LAVar( e, var, *p_v, revert );
      //      slack_vars.push_back( x );
      enode_lavar[var->getId( )] = x;

      if( x->ID( ) >= static_cast<int> ( columns.size( ) ) )
        columns.resize( x->ID( ) + 1, NULL );
      columns[x->ID( )] = x;

      if( e->getId( ) >= ( int )enode_lavar.size( ) )
        enode_lavar.resize( e->getId( ) + 1, NULL );
      enode_lavar[e->getId( )] = x;
    }
    else
    {
      x = enode_lavar[var->getId( )];
      x->setBounds( e, *p_v, revert );

      if( e->getId( ) >= ( int )enode_lavar.size( ) )
        enode_lavar.resize( e->getId( ) + 1, NULL );
      enode_lavar[e->getId( )] = x;
    }

    numbers_pool.push_back( p_v );
  }
  // parse the Plus enode of the contraint
  else if( arg2->isPlus( ) )
  {
    if( arg2->getId( ) >= ( int )enode_lavar.size( ) )
      enode_lavar.resize( arg2->getId( ) + 1, NULL );

    if( enode_lavar[arg2->getId( )] != NULL )
    {
      LAVar * x = enode_lavar[arg2->getId( )];
      x->setBounds( e, arg1 );

      if( e->getId( ) >= ( int )enode_lavar.size( ) )
        enode_lavar.resize( e->getId( ) + 1, NULL );
      enode_lavar[e->getId( )] = x;
    }
    else
    {
      // introduce the slack variable with bounds on it
      LAVar * s = new LAVar( e, arg1, arg2, true );
      slack_vars.push_back( s );

      assert( s->basicID( ) != -1 );

      if( s->ID( ) >= static_cast<int> ( columns.size( ) ) )
        columns.resize( s->ID( ) + 1, NULL );
      columns[s->ID( )] = s;

      if( s->basicID( ) >= static_cast<int> ( rows.size( ) ) )
        rows.resize( s->basicID( ) + 1, NULL );
      rows[s->basicID( )] = s;

      Real * p_r;
      if( !numbers_pool.empty( ) )
      {
        p_r = numbers_pool.back( );
        numbers_pool.pop_back( );
        *p_r = Real( -1 );
      }
      else
      {
        p_r = new Real( -1 );
      }

      s->polynomial.add( s->ID( ), 0, p_r );

      if( e->getId( ) >= ( int )enode_lavar.size( ) )
        enode_lavar.resize( e->getId( ) + 1, NULL );
      enode_lavar[e->getId( )] = s;

      if( arg2->getId( ) >= ( int )enode_lavar.size( ) )
        enode_lavar.resize( arg2->getId( ) + 1, NULL );
      enode_lavar[arg2->getId( )] = s;

      Enode * list = arg2->getCdr( );

      //reads the argument of +
      while( !list->isEnil( ) )
      {
        Enode * p = list->getCar( );
        // If p is a monome ai*xi
        if( p->isTimes( ) )
        {
          arg1 = p->get1st( );
          arg2 = p->get2nd( );

          assert( config.logic != QF_LRA || arg1->isVar( ) || arg2->isVar( ) );
          assert( config.logic != QF_LIA || arg1->isVar( ) || arg2->isVar( ) );
          assert( config.logic != QF_UFLRA || arg1->isVar( ) || arg2->isVar( ) || arg1->isUf( ) || arg2->isUf( ) );

          // We store variable in var, coefficient in num
          Enode * var = arg1->isVar( ) || arg1->isUf( ) ? arg1 : arg2;
          Enode * num = arg1->isVar( ) || arg1->isUf( ) ? arg2 : arg1;

          // Get the coefficient
          if( !numbers_pool.empty( ) )
          {
            p_r = numbers_pool.back( );
            numbers_pool.pop_back( );
            *p_r = Real( num->getComplexValue( ) );
          }
          else
          {
            p_r = new Real( num->getComplexValue( ) );
          }

          // check if we need a new LAVar for a given var
          LAVar * x = NULL;

          if( var->getId( ) >= ( int )enode_lavar.size( ) )
            enode_lavar.resize( var->getId( ) + 1, NULL );

          if( enode_lavar[var->getId( )] != NULL )
          {
            x = enode_lavar[var->getId( )];
            addVarToRow( s, x, p_r );
          }
          else
          {
            x = new LAVar( var );
            slack_vars.push_back( x );
            enode_lavar[var->getId( )] = x;

            if( x->ID( ) >= static_cast<int> ( columns.size( ) ) )
              columns.resize( x->ID( ) + 1, NULL );
            columns[x->ID( )] = x;

            x->binded_rows.add( s->basicID( ), s->polynomial.add( x->ID( ), x->binded_rows.free_pos( ), p_r ) );
          }

          assert( x );
          assert( s->basicID( ) != -1 );

        }
        list = list->getCdr( );
      }
    }
  }
  else
  {
    opensmt_error2( "Unexpected atom: ", e );
  }
#if VERBOSE
  cout << "Informed of constraint " << e << endl;
  //  cout << this << endl;
#endif
  return l_Undef;
}

//
// Performs the main Check procedure to see if the current constraints and Tableau are satisfiable
//
bool LRASolver::check( bool complete )
{

  ( void )complete;
  // check if we stop reading constraints
  if( status == INIT )
    initSolver( );

  LAVar * x = NULL;

  VectorLAVar hist_x;
  VectorLAVar hist_y;
  bool bland_rule = false;
  unsigned pivot_counter = 0;

  // keep doing pivotAndUpdate until the SAT/UNSAT status is confirmed
  while( 1 )
  {
    // clear the explanations vector
    explanation.clear( );
    explanationCoefficients.clear( );

    x = NULL;

    if( !bland_rule && ( pivot_counter++ > columns.size( ) ) )
    {
      //     cout << "pivot_counter exceeded: " << pivot_counter <<endl;
      bland_rule = true;
    }
    // look for the basic x with the smallest index which doesn't feat the bounds
    VectorLAVar::const_iterator it = rows.begin( );
    for( ; it != rows.end( ); ++it )
    {
      if( ( *it )->isModelOutOfBounds( ) )
      {
        if( bland_rule )
        {
          x = *it;
          break;
        }
        else
        {
          if( x == NULL )
          {
            x = *it;
            //            tmp_d = x->overBound( );
          }
          else if( x->polynomial.size( ) > ( *it )->polynomial.size( ) )
          //          else if( tmp_d > ( *it )->overBound( )  || tmp_d == ( *it )->overBound( ) && x->polynomial.size() > (*it)->polynomial.size())
          //          else if( x->polynomial.size() > (*it)->polynomial.size() || (x->polynomial.size() == (*it)->polynomial.size() && x->overBound( ) > ( *it )->overBound( )) )
          {
            x = *it;
            //            tmp_d = x->overBound( );
          }
        }
      }
    }

//     If not found, check if problem refinement for integers is required
        if( config.lra_integer_solver && complete && x == NULL )
          return checkIntegersAndSplit( );
        // Otherwise - SAT
        else
          if( x == NULL )
    {
      refineBounds( );
      LAVar::saveModelGlobal( );
      if( checks_history.back( ) < pushed_constraints.size( ) )
        checks_history.push_back( pushed_constraints.size( ) );
//      cout << "USUAL SAT" << endl;
      return setStatus( SAT );
    }

    Real * a;
    LAVar * y = NULL;
    LAVar * y_found = NULL;

    // Model doesn't feet the lower bound
    if( x->M( ) < x->L( ) )
    {
      // look for nonbasic terms to fix the unbounding
      LARow::iterator it = x->polynomial.begin( );
      for( ; it != x->polynomial.end( ); x->polynomial.getNext( it ) )
      {
        y = columns[it->key];
        if( x == y )
          continue;
//        cout << *y << " for " << *x <<  " : " << y->L() << " <= " << y->M() << " <= " << y->U()<< endl;

        assert( y->isNonbasic( ) );
        a = it->coef;
        const bool & a_is_pos = ( *a ) > 0;
        if( ( a_is_pos && y->M( ) < y->U( ) ) || ( !a_is_pos && y->M( ) > y->L( ) ) )
        {
          if( bland_rule )
          {
            y_found = y;
            break; // stop on the very first that feats
          }
          else
          {
            if( y_found == NULL )
              y_found = y;
            else if( y_found->binded_rows.size( ) > y->binded_rows.size( ) )
              y_found = y;
          }
        }
      }

      // if it was not found - UNSAT
      if( y_found == NULL )
      {
//                cout << "NO ways to SAT" << endl;
        getConflictingBounds( x, explanation );
        //TODO: Keep the track of updated models and restore only them
        for( unsigned i = 0; i < columns.size( ); ++i )
          if( !columns[i]->skip )
            columns[i]->restoreModel( );
        return setStatus( UNSAT );
      }
      // if it was found - pivot old Basic x with non-basic y and do the model updates
      else
        pivotAndUpdate( x, y_found, x->L( ) );
    }
    else if( x->M( ) > x->U( ) )
    {
      // look for nonbasic terms to fix the unbounding
      LARow::iterator it = x->polynomial.begin( );
      for( ; it != x->polynomial.end( ); x->polynomial.getNext( it ) )
      {
        y = columns[it->key];
        if( x == y )
          continue;
//        cout << *y << " for " << *x <<  " : " << y->L() << " <= " << y->M() << " <= " << y->U()<< endl;

        assert( y->isNonbasic( ) );
        a = it->coef;
        const bool & a_is_pos = ( *a ) > 0;
        if( ( !a_is_pos && y->M( ) < y->U( ) ) || ( a_is_pos && y->M( ) > y->L( ) ) )
        {
          if( bland_rule )
          {
            y_found = y;
            break; // stop on the very first that feats
          }
          else
          {
            if( y_found == NULL )
              y_found = y;
            else if( y_found->binded_rows.size( ) > y->binded_rows.size( ) )
              y_found = y;
          }
        }
      }

      // if it was not found - UNSAT
      if( y_found == NULL )
      {
//                cout << "NO ways to SAT 2" << endl;
        // add the x to explanations
        getConflictingBounds( x, explanation );
        for( unsigned i = 0; i < columns.size( ); ++i )
          if( !columns[i]->skip )
            columns[i]->restoreModel( );
        return setStatus( UNSAT );
      }
      // if it was found - pivot old Basic x with non-basic y and do the model updates
      else
        pivotAndUpdate( x, y_found, x->U( ) );
    }
    else
    {
      opensmt_error( "Error in bounds comparison" );
    }
  }
}

//
// Push the constraint into the solver and increase the level
//
bool LRASolver::assertLit( Enode * e, bool reason )
{
  ( void )reason;
  // check if we stop reading constraints
  if( status == INIT )
    initSolver( );

  assert( e->hasPolarity( ) );

//    cout << "Pushing (" << ( e->getPolarity( ) == l_True ) << ") (" << ( e->getDeduced( ) == l_True ) << ")  [" << e->getDedIndex( ) << "/" << id << "] " << e
//        << " - " << enode_lavar[e->getId( )] << endl;

  bool is_reason = false;

  // skip if it was deduced by the solver itself with the same polarity
  if( e->isDeduced( ) && e->getDeduced( ) == e->getPolarity( ) && e->getDedIndex( ) == id )
    return getStatus( );
  else if( e->isDeduced( ) && e->getDedIndex( ) == id )
    is_reason = true;

  LAVar* it = enode_lavar[e->getId( )];
  
  // Constraint to push was not find in local storage. Most likely it was not read properly before
  if ( it == NULL )
    opensmt_error( "Unexpected push !" );

  assert( !it->isUnbounded( ) );
  unsigned it_i = it->getIteratorByEnode( e, e->getPolarity( ) == l_False );

  if( assertBoundOnColumn( it, it_i ) )
  {
    if( config.lra_theory_propagation == 1 && !is_reason )
    {
      it->getSimpleDeductions( deductions, id, it->all_bounds[it_i].bound_type );
    }
    if( config.lra_check_on_assert != 0 && rand( ) % 100 < config.lra_check_on_assert )
    {
      // force solver to do check on assert with some probability
      return check( false );
    }
  }
  return getStatus( );
}

////
//// Push the constraint into the solver and increase the level
////
//bool LRASolver::assertLitPolarity( Enode * e, bool polarity, bool is_reason )
//{
//
//  ( void )is_reason;
//  // check if we stop reading constraints
//  if( status == INIT )
//    initSolver( );
//
//  //  assert( e->hasPolarity( ) );
//
//  cerr << "Pushing (" << ( e->getPolarity( ) == l_True ) << ") (" << ( e->getDeduced( ) == l_True ) << ")  [" << e->getDedIndex( ) << "/" << id << "] " << e
//      << " - " << enode_lavar[e->getId( )] << endl;
//
//  //  bool is_reason = false;
//  //
//  //  // skip if it was deduced by the solver itself with the same polarity
//  //  if( e->isDeduced( ) && e->getDeduced( ) == e->getPolarity( ) && e->getDedIndex( ) == id )
//  //    return getStatus( );
//  //  else if( e->isDeduced( ) && e->getDedIndex( ) == id )
//  //    is_reason = true;
//
//  assert( status != UNSAT );
//
//  // Look for the constraint to push
//  LAVar* it = enode_lavar[e->getId( )];
//
//  if( it != NULL )
//  {
//    assert( !it->isUnbounded( ) );
//    unsigned it_i = it->getIteratorByEnode( e, !polarity );
//
//    if( !assertBoundOnColumn( it, it_i ) )
//    {
//      if( config.lra_theory_propagation == 1 && !is_reason )
//      {
//        it->getSimpleDeductions( deductions, id, itBound.bound_type );
//      }
//    }
//    return getStatus( );
//
////    if( config.lra_check_on_assert != 0 && rand( ) % 100 < config.lra_check_on_assert )
////    {
////      // force solver to do check on assert with some probability
////      return check( false );
////    }
////    else
//
//  }
//  // Constraint to push was not find in local storage. Most likely it was not read properly before
//  else
//  {
//    error( "Unexpected push! ", "" );
//    return setStatus( ERROR );
//  }
//}

bool LRASolver::assertBoundOnColumn( LAVar * it, unsigned it_i )
{
  assert( status == SAT );
  assert( it != NULL );
  assert( !it->isUnbounded( ) );
  LAVar::LAVarBound &itBound = it->all_bounds[it_i];

//  cout << "ASSERTING bound on " << *it << endl;

  // Check is simple SAT can be given
  if( ( itBound.bound_type && it_i >= it->u_bound ) || ( !itBound.bound_type && it_i <= it->l_bound ) )
  {
    if( checks_history.back( ) < pushed_constraints.size( ) )
    {
//      cout << "PUSH CHECK " << checks_history.back( ) << " " << pushed_constraints.size( ) << endl;
      checks_history.push_back( pushed_constraints.size( ) );
    }
//    cout << "SIMPLE SAT" << endl;
    return getStatus( );
  }
  // Check if simple UNSAT can be given
  if( ( !itBound.bound_type && ( it_i > it->u_bound ) ) || ( itBound.bound_type && ( it_i < it->l_bound ) ) )
  {
    explanation.clear( );
    explanationCoefficients.clear( );

    if( itBound.bound_type && it->all_bounds[it->l_bound].e != NULL )
    {
      explanation.push_back( it->all_bounds[it->l_bound].e );
      explanationCoefficients.push_back( Real( 1 ) );
    }
    else if( !itBound.bound_type && it->all_bounds[it->u_bound].e != NULL )
    {
      explanation.push_back( it->all_bounds[it->u_bound].e );
      explanationCoefficients.push_back( Real( 1 ) );
    }

    if( itBound.e != NULL )
    {
      explanation.push_back( itBound.e );
      explanationCoefficients.push_back( Real( 1 ) );
    }
//    cout << "SIMPLE UNSAT" << endl;
    return setStatus( UNSAT );
  }

//  cout << "write history" << endl;
  // Prepare the history entry
  LAVarHistory &hist = pushed_constraints.back( );
  hist.e = itBound.e;
  hist.v = it;
  hist.bound_type = itBound.bound_type;
  if( itBound.bound_type )
  {
    hist.bound = it->u_bound;
    it->u_bound = it_i;
  }
  else
  {
    hist.bound = it->l_bound;
    it->l_bound = it_i;
  }
  // Update the Tableau data if needed
  if( it->isNonbasic( ) )// && *( itBound.delta ) < it->M( ) ) // && *( itBound.delta ) > it->M( ) )
  {
    update( it, *( itBound.delta ) );
  }

  // LAVar *x = it;
//  cout << "ASSERTED bound on " << *x << ": " << x->L( ) << " <= " << x->M( ) << " <= " << x->U( ) << endl;

  //  cout << "NORMAL " << status <<endl;
  return getStatus( );
  //  return check(true);
}

//
// Push the solver one level down
//
void LRASolver::pushBacktrackPoint( )
{
//  cout << "push " << pushed_constraints.size( ) << endl;
  // Check if any updates need to be repeated after backtrack
  if( first_update_after_backtrack )
  {
//    cout << "re-apply " << pushed_constraints.size( ) << " - " << checks_history.back( ) << endl;
    for( unsigned i = checks_history.back( ); i < pushed_constraints.size( ); i++ )
    {
      LAVar * v = pushed_constraints[i].v;
      if( v != NULL && v->isNonbasic( ) && v->isModelOutOfBounds( ) )
      {
        if( v->isModelOutOfUpperBound( ) )
          update( v, v->U( ) );
        else
          update( v, v->L( ) );
      }
    }
    //          assertBoundOnColumn(pushed_constraints[i].v, pushed_constraints[i].bound, true);
    //        assertLit( pushed_constraints[i].e, false );

//    for( unsigned i = 0; i < checks_history.size( ); i++ )
//      cout << checks_history[i] << " ";
//    cout << endl;
    //    assert(checks_history.back( ) == pushed_constraints.size( ));
    first_update_after_backtrack = false;
  }

  // Create and push new history step
  LAVarHistory hist;
  hist.e = NULL;
  hist.v = NULL;
  pushed_constraints.push_back( hist );
}

//
// Pop the solver one level up
//
void LRASolver::popBacktrackPoint( )
{
//  cout << "pop " << pushed_constraints.size( ) << endl;

  // Undo with history
  LAVarHistory &hist = pushed_constraints.back( );

  if( hist.v != NULL )
  {
    if( hist.bound_type )
      hist.v->u_bound = hist.bound;
    else
      hist.v->l_bound = hist.bound;
  }

  //TODO: Keep an eye on SAT model crossing the bounds of backtracking
  //  if( status == UNSAT && checks_history.back( ) == pushed_constraints.size( ) )
  if( checks_history.back( ) == pushed_constraints.size( ) )
  {
//    cout << "POP CHECKS " << checks_history.back( ) << endl;
    checks_history.pop_back( );
  }
  first_update_after_backtrack = true;

  pushed_constraints.pop_back( );

  setStatus( SAT);
}

//
// Look for unbounded terms and applies Gaussian elimination to them. Delete the column if succeeded
//
void LRASolver::doGaussianElimination( )
{
  int m;

  for( unsigned i = 0; i < columns.size( ); ++i )
    if( !columns[i]->skip && columns[i]->isNonbasic( ) && columns[i]->isUnbounded( ) && columns[i]->binded_rows.size( ) > 1 )
    {
      LAVar * x = columns[i];

      LAColumn::iterator it = x->binded_rows.begin( );

      assert( it != x->binded_rows.end( ) );

      int basisRow = it->key;
      LAVar * basis = rows[basisRow];

      Real a = Real( *( rows[it->key]->polynomial[it->pos_in_row].coef ) );
      Real ratio = 0;

      x->binded_rows.getNext( it );

      assert( it != x->binded_rows.end( ) );

      for( ; it != x->binded_rows.end( ); x->binded_rows.getNext( it ) )
      {
        ratio = Real( ( *( rows[it->key]->polynomial[it->pos_in_row].coef ) ) / a );
        for( LARow::iterator it2 = basis->polynomial.begin( ); it2 != basis->polynomial.end( ); basis->polynomial.getNext( it2 ) )
        {
          LARow::iterator a_it = rows[it->key]->polynomial.find( it2->key );
          if( a_it == rows[it->key]->polynomial.end( ) )
          {
            Real * c = NULL;
            if( !numbers_pool.empty( ) )
            {
              c = numbers_pool.back( );
              numbers_pool.pop_back( );
              *c = -ratio * ( *( basis->polynomial.find( it2->key )->coef ) );
            }
            else
            {
              c = new Real( -ratio * ( *( basis->polynomial.find( it2->key )->coef ) ) );
            }
            columns[it2->key]->binded_rows.add( it->key, rows[it->key]->polynomial.add( it2->key, columns[it2->key]->binded_rows.free_pos( ), c ) );
          }
          else
          {
            *( a_it->coef ) -= ( *( basis->polynomial.find( it2->key )->coef ) ) * ratio;
            if( *( a_it->coef ) == 0 )
            {
              assert( a_it->coef );
              // Store removed Real in memory pool
              numbers_pool.push_back( a_it->coef );
              if( it2->key != x->ID( ) )
                columns[it2->key]->binded_rows.remove( a_it->pos );
              rows[it->key]->polynomial.remove( a_it );
            }
          }
        }
      }

      // Clear removed row
      for( LARow::iterator it2 = basis->polynomial.begin( ); it2 != basis->polynomial.end( ); basis->polynomial.getNext( it2 ) )
      {
        if( it2->key != basis->ID( ) )
        {
          columns[it2->key]->unbindRow( basisRow );
        }
        assert( it2->coef );
      }

      // Keep polynomial in x to compute a model later
      assert( x->polynomial.empty( ) );
      swap( basis->polynomial, x->polynomial );
      removed_by_GaussianElimination.push_back( x );
      x->binded_rows.clear( );
      x->skip = true;

      // Replace basisRow slot with the last row in rows vector
      m = rows.size( ) - 1;
      if( m > basisRow )
      {
        for( LARow::iterator it2 = rows[m]->polynomial.begin( ); it2 != rows[m]->polynomial.end( ); rows[m]->polynomial.getNext( it2 ) )
        {
          if( it2->key != rows[m]->ID( ) )
          {
            columns[it2->key]->binded_rows.remove( it2->pos );
            columns[it2->key]->binded_rows.add( basisRow, rows[m]->polynomial.getPos( it2 ) );
          }
        }

        rows[basisRow] = rows[m];
        rows[m]->setBasic( basisRow );
      }
      basis->setNonbasic( );
      rows.pop_back( );
    }
}

//
// updates the model values according to asserted bound
//
void LRASolver::update( LAVar * x, const Delta & v )
{
  // update model value for all basic terms
  const Delta & v_minusM = v - x->M( );
  for( LAColumn::iterator it = x->binded_rows.begin( ); it != x->binded_rows.end( ); x->binded_rows.getNext( it ) )
  {
    LAVar & row = *( rows[it->key] );
    row.incM( *( row.polynomial[it->pos_in_row].coef ) * v_minusM );

    if( static_cast<int> ( row.polynomial.size( ) ) <= config.lra_poly_deduct_size )
      touched_rows.insert( rows[it->key] );

    //TODO: make a separate config value for suggestions
    //TODO: sort the order of suggestion requesting based on metric (Model increase, out-of-bound distance etc)
    //    if( config.lra_theory_propagation == 3 )
    //    {
    //      if( suggestions.empty( ) )
    //        rows[it->key]->getSuggestions( suggestions, id );
    //    }
  }
  x->setM( v );
//  cout << "UPDATED nonbasic " << *x << ": " << x->L( ) << " <= " << x->M( ) << " <= " << x->U( ) << endl;
}

//
// pivots x and y in solver and does all updates
//
void LRASolver::pivotAndUpdate( LAVar * x, LAVar * y, const Delta & v )
{
//  std::cout << "PIVOT AND UPDATE" << *x << " - " << *y << " - " << v << endl;
  assert( x != y );
  assert( x->isBasic( ) );
  assert( y->isNonbasic( ) );

  assert( y->polynomial.empty( ) );
  assert( x->binded_rows.empty( ) );
  assert( x->polynomial.exists( y->ID( ) ) );

  // get Tetta (zero if Aij is zero)
  const Real & a = *( x->polynomial.find( y->ID( ) )->coef );
  assert( a != 0 );
  Delta tetha = ( v - x->M( ) ) / a;

  // update models of x and y
  x->setM( v );
  y->incM( tetha );

  // update model of Basic variables
  for( LAColumn::iterator it = y->binded_rows.begin( ); it != y->binded_rows.end( ); y->binded_rows.getNext( it ) )
  {

    if( rows[it->key] != x )
    {
      LAVar & row = *( rows[it->key] );
      row.incM( *( row.polynomial[it->pos_in_row].coef ) * tetha );
      if( static_cast<int> ( row.polynomial.size( ) ) <= config.lra_poly_deduct_size )
        touched_rows.insert( rows[it->key] );
    }
  }
  // pivoting x and y

#if FAST_RATIONALS
  const Real & inverse = -FastRational_inverse( a );
#else
  const Real & inverse = -1 / a;
#endif

  // NEW VARIANT OF PIVOTING

  //  for( LARow::iterator it = x->polynomial.begin( ); it != x->polynomial.end( ); x->polynomial.getNext( it ) )
  //  {
  //    // first inverse the coeff of the pivoting row
  //    *( it->coef ) *= inverse;
  //
  //    assert( it->key != y->ID( ) || ( *( x->polynomial.find( y->ID( ) )->coef ) == -1 ) );
  //
  //    const Real &b = *( it->coef );
  //    assert( b != 0 );
  //
  //    for( LARow::iterator it2 = y->binded_rows.begin( ); it2 != y->binded_rows.end( ); y->binded_rows.getNext( it2 ) )
  //    {
  //      // skip the pivoting column and row for now
  //      if( it2->key == x->basicID( ) || it->key == y->ID( ) )
  //        continue;
  //      else
  //      {
  //        assert( it->key != y->ID( ) );
  //        assert( it2->key != x->basicID( ) );
  //
  //        const Real &a = *( it2->coef );
  //        assert( a != 0 );
  //
  //        // add to existing coefficient
  //        if( rows[it2->key]->polynomial.exists( it->key ) )
  //        //        if( columns[it->key]->binded_rows.exists( it2->key ) )
  //        {
  ////          if( columns[it->key]->binded_rows.size( ) > rows[it2->key]->polynomial.size( ) )
  ////            cout << 1 ;
  ////          else
  ////            cout << 0;
  ////            cout << columns[it->key]->binded_rows.size( ) << " vs " << rows[it2->key]->polynomial.size( ) << endl;
  ////          LARow::iterator c_it = columns[it->key]->binded_rows.findfast( it2->key );
  ////          assert (c_it!=columns[it->key]->binded_rows.end());
  ////          Real * p_c = c_it->coef;
  ////          *( p_c ) += b * a;
  ////          // delete element from P_i if it become 0
  ////          if( *( p_c ) == 0 )
  ////          {
  ////            // Save Real in pool
  ////            numbers_pool.push_back( p_c );
  ////            // Mark out the value from column and row
  ////            rows[it2->key]->polynomial.remove( c_it->pos );
  ////            assert( it->key != y->ID( ) );
  ////            columns[it->key]->binded_rows.remove( c_it );
  ////          }
  //
  ////
  //          LARow::iterator c_it = rows[it2->key]->polynomial.findfast( it->key );
  //          assert (c_it!=rows[it2->key]->polynomial.end());
  //          Real * p_c = c_it->coef;
  //          *( p_c ) += b * a;
  //          // delete element from P_i if it become 0
  //          if( *( p_c ) == 0 )
  //          {
  //            // Save Real in pool
  //            numbers_pool.push_back( p_c );
  //            // Mark out the value from column and row
  ////            assert( it->key != y->ID( ) );
  //            columns[it->key]->binded_rows.remove( c_it->pos );
  //            rows[it2->key]->polynomial.remove( c_it);
  //          }
  //
  //        }
  //        // or insert new element to P_i
  //        else
  //        {
  //          // handle reals via memory pool
  //          Real * p_c = NULL;
  //          if( !numbers_pool.empty( ) )
  //          {
  //            p_c = numbers_pool.back( );
  //            numbers_pool.pop_back( );
  //            *p_c = a * b;
  //          }
  //          else
  //          {
  //            p_c = new Real( a * b );
  //          }
  //          columns[it->key]->binded_rows.add( it2->key, rows[it2->key]->polynomial.add( it->key, columns[it->key]->binded_rows.free_pos( ), p_c ), p_c );
  //        }
  //      }
  //
  //      // mark the affected row (for deductions)
  //      if( static_cast<int> ( rows[it2->key]->polynomial.size( ) ) <= config.lra_poly_deduct_size )
  //        touched_rows.insert( rows[it2->key] );
  //    }
  //  }
  //
  //  //clean the position y in all the rows
  //  for( LARow::iterator it2 = y->binded_rows.begin( ); it2 != y->binded_rows.end( ); y->binded_rows.getNext( it2 ) )
  //  {
  //    if( it2->key != x->basicID( ) )
  //    {
  //      numbers_pool.push_back( it2->coef );
  //      assert( rows[it2->key]->polynomial.find( y->ID() ) != rows[it2->key]->polynomial.end( ) );
  //      LARow::iterator it = rows[it2->key]->polynomial.find( y->ID() );
  //      assert( rows[it2->key]->polynomial[it2->pos].key == y->ID() );
  //      rows[it2->key]->polynomial.remove( it2->pos );
  //    }
  //  }

  // OLD PIVOTING
  // first change the attribute values for x  polynomial
  for( LARow::iterator it = x->polynomial.begin( ); it != x->polynomial.end( ); x->polynomial.getNext( it ) )
    *( it->coef ) *= inverse;

  // value of a_y should become -1
  assert( !( *( x->polynomial.find( y->ID( ) )->coef ) != -1 ) );

  // now change the attribute values for all rows where y was presented
  for( LAColumn::iterator it = y->binded_rows.begin( ); it != y->binded_rows.end( ); y->binded_rows.getNext( it ) )
  {
    // check that the modified row is not x (it was changed already)
    if( rows[it->key] != x )
    {
      LAVar & row = *( rows[it->key] );

      assert( *( row.polynomial[it->pos_in_row].coef ) != 0 );

      // copy a to the new Real variable (use memory pool)
      //TODO: make a function for the code below
      Real * p_a = NULL;
      if( !numbers_pool.empty( ) )
      {
        p_a = numbers_pool.back( );
        numbers_pool.pop_back( );
        *p_a = *( row.polynomial[it->pos_in_row].coef );
      }
      else
      {
        p_a = new Real( *( row.polynomial[it->pos_in_row].coef ) );
      }

      const Real& a = *( p_a );

      // P_i = P_i + a_y * P_x (iterate over all elements of P_x)
      for( LARow::iterator it2 = x->polynomial.begin( ); it2 != x->polynomial.end( ); x->polynomial.getNext( it2 ) )
      {
        LAVar & col = *( columns[it2->key] );

        const Real &b = *( it2->coef );
        assert( b != 0 );
        // insert new element to P_i
        if( !row.polynomial.exists( it2->key ) )
        {
          // handle reals via memory pool
          Real * p_c = NULL;
          if( !numbers_pool.empty( ) )
          {
            p_c = numbers_pool.back( );
            numbers_pool.pop_back( );
            *p_c = a * b;
          }
          else
          {
            p_c = new Real( a * b );
          }
          col.binded_rows.add( it->key, row.polynomial.add( it2->key, col.binded_rows.free_pos( ), p_c ) );
        }
        // or add to existing
        else
        {
          LARow::iterator a_it = row.polynomial.find( it2->key );
          assert( a_it != row.polynomial.end( ) );
          *( a_it->coef ) += b * a;
          if( *( a_it->coef ) == 0 )
          {
            // delete element from P_i if it become 0
            assert( a_it->coef );

            // Save Real in pool
            numbers_pool.push_back( a_it->coef );

            // Mark out the value from column and row
            if( it2->key != y->ID( ) )
              col.binded_rows.remove( a_it->pos );
            row.polynomial.remove( a_it );
          }
        }
      }
      numbers_pool.push_back( p_a );

      assert( ( row.polynomial.find( y->ID( ) ) == row.polynomial.end( ) ) );

      // mark the affected row (for deductions)
      if( static_cast<int> ( row.polynomial.size( ) ) <= config.lra_poly_deduct_size )
        touched_rows.insert( rows[it->key] );
    }
  }

  // swap x and y (basicID, polynomial, bindings)
  swap( x->polynomial, y->polynomial );
  assert( x->polynomial.empty( ) );
  assert( !y->polynomial.empty( ) );
  y->setBasic( x->basicID( ) );
  x->setNonbasic( );
  rows[y->basicID( )] = y;

  assert( y->polynomial.find( x->ID( ) ) != y->polynomial.end( ) );
  assert( y->polynomial.find( x->ID( ) )->pos >= 0 );
  assert( y->polynomial.find( x->ID( ) ) != y->polynomial.end( ) );
  const LARow::iterator tmp_it = y->polynomial.find( x->ID( ) );
  tmp_it->pos = x->binded_rows.free_pos( );
  x->binded_rows.add( y->basicID( ), y->polynomial.getPos( tmp_it ) );
  y->binded_rows.clear( );

  if( static_cast<int> ( y->polynomial.size( ) ) <= config.lra_poly_deduct_size )
    touched_rows.insert( y );
  touched_rows.erase( x );

  assert( x->polynomial.size( ) == 0 );
  assert( y->polynomial.size( ) > 0 );
  assert( x->binded_rows.size( ) > 0 );
}

//
// Perform all the required initialization after inform is complete
//
void LRASolver::initSolver( )
{
  if( status == INIT )
  {
    // Gaussian Elimination should not be performed in the Incremental mode!
    if( config.lra_gaussian_elim == 1 )
      doGaussianElimination( );

    //                 sort the bounds inserted during inform stage
//    for( unsigned it = 0; it < columns.size( ); it++ )
//      if( !( columns[it]->skip ) )
//        columns[it]->printBounds( );
//    cout << endl;

    status = SAT;

    // used to apply checks in assertLit with a given probability
    //    srand ( time( NULL ));
  }
  else
    opensmt_error( "Solver can not be initialized in the state different from INIT" );
}

//
// Returns boolean value correspondent to the current solver status
//
inline bool LRASolver::getStatus( )
{
  switch( status )
  {
  case SAT:
  {
    return true;
    break;
  }
  case UNSAT:
  {
    return false;
    break;
  }
  case INIT:
  case ERROR:
  default:
    opensmt_error( "Status is undef!" );
    return false;
  }
}

//
// Sets the new solver status and returns the correspondent lbool value
//
inline bool LRASolver::setStatus( LRASolverStatus s )
{
  status = s;
  return getStatus( );
}

//
// Returns the bounds conflicting with the actual model.
//
void LRASolver::getConflictingBounds( LAVar * x, vector<Enode *> & dst )
{

  LAVar * y;
  if( x->M( ) < x->L( ) )
  {
    // add all bounds for polynomial elements, which limit lower bound
    LARow::iterator it = x->polynomial.begin( );
    for( ; it != x->polynomial.end( ); x->polynomial.getNext( it ) )
    {
      const Real a = *(it->coef);
      y = columns[it->key];
      assert( a != 0 );
      if( x == y )
      {
        assert( y->all_bounds[y->l_bound].e != NULL );

        dst.push_back( y->all_bounds[y->l_bound].e );
        explanationCoefficients.push_back( Real( 1 ) );
      }
      else if( a < 0 )
      {
        assert( !y->L( ).isInf( ) );
        assert( y->all_bounds[y->l_bound].e != NULL );

        dst.push_back( y->all_bounds[y->l_bound].e );
        explanationCoefficients.push_back( -a );
      }
      else
      {
        assert( !y->U( ).isInf( ) );
        assert( y->all_bounds[y->u_bound].e != NULL );

        dst.push_back( y->all_bounds[y->u_bound].e );
        explanationCoefficients.push_back( a );
      }
    }
  }
  if( x->M( ) > x->U( ) )
  {
    // add all bounds for polynomial elements, which limit upper bound
    LARow::iterator it = x->polynomial.begin( );
    for( ; it != x->polynomial.end( ); x->polynomial.getNext( it ) )
    {
      const Real a = *(it->coef);
      y = columns[it->key];
      assert( a != 0 );
      if( x == y )
      {
        assert( y->all_bounds[y->u_bound].e != NULL );

        dst.push_back( y->all_bounds[y->u_bound].e );
        explanationCoefficients.push_back( Real( 1 ) );
      }
      else if( a > 0 )
      {
        assert( !y->L( ).isInf( ) );
        assert( y->all_bounds[y->l_bound].e != NULL );

        dst.push_back( y->all_bounds[y->l_bound].e );
        explanationCoefficients.push_back( a );
      }
      else
      {
        assert( !y->U( ).isInf( ) );
        assert( y->all_bounds[y->u_bound].e != NULL );

        dst.push_back( y->all_bounds[y->u_bound].e );
        explanationCoefficients.push_back( -a );
      }
    }
  }

  assert( dst.size( ) == x->polynomial.size( ) );
}

//
// Compute the current bounds for each row and tries to deduce something useful
//
void LRASolver::refineBounds( )
{

  // Check if polynomial deduction is enabled
  if( config.lra_poly_deduct_size == 0 )
    return;

  // iterate over all rows affected in the current check
  for( set<LAVar *>::const_iterator t_it = touched_rows.begin( ); t_it != touched_rows.end( ); ++t_it )
  {
    assert( ( *t_it )->isBasic( ) );
    LAVar * row = *t_it;

    bool UpInf = false; // become true when polynomial is infinite on the upper bound
    bool LoInf = false; // become true when polynomial is infinite on the lower bound
    bool UpExists = false; // flag is used to track if Up was initialized
    bool LoExists = false; // flag is used to track if Lo was initialized
    Delta Up( Delta::ZERO ); // upper bound value
    Delta Lo( Delta::ZERO ); // lower bound value
    int UpInfID = -1; // used to track the ID of the only element with infinite upper bound
    int LoInfID = -1; // used to track the ID of the only element with infinite lower bound

    // summarize all bounds for the polynomial
    for( LARow::iterator it = row->polynomial.begin( ); it != row->polynomial.end( ); row->polynomial.getNext( it ) )
    {
      Real & a = ( *( it->coef ) );
      LAVar * col = columns[it->key];

      assert( a != 0 );
      bool a_lt_zero = a < 0;

      // check if the upper (lower) bound is infinite or can be added to the summarized value of the upper bound
      if( !UpInf && ( ( col->U( ).isPlusInf( ) && !a_lt_zero ) || ( col->L( ).isMinusInf( ) && a_lt_zero ) ) )
      {
        if( UpInfID == -1 )
          UpInfID = col->ID( ); // one element can be unbounded
        else
          UpInf = true; // no upper bound exists
      }
      else if( !UpInf )
      {
        // add lower or upper bound (depending on the sign of a_i)
        if( UpExists )
          Up += a * ( a_lt_zero ? col->L( ) : col->U( ) );
        else
        {
          Up = a * ( a_lt_zero ? col->L( ) : col->U( ) );
          UpExists = true;
        }
      }

      // check if the lower (upper) bound is infinite or can be added to the summarized value of the lower bound
      if( !LoInf && ( ( col->U( ).isPlusInf( ) && a_lt_zero ) || ( col->L( ).isMinusInf( ) && !a_lt_zero ) ) )
      {
        if( LoInfID == -1 ) // one element can be unbounded
          LoInfID = col->ID( );
        else
          LoInf = true; // no lower bound exists
      }
      else if( !LoInf )
      {
        // add lower or upper bound (depending on the sign of a_i)
        if( LoExists )
          Lo += a * ( !a_lt_zero ? col->L( ) : col->U( ) );
        else
        {
          Lo = a * ( !a_lt_zero ? col->L( ) : col->U( ) );
          LoExists = true;
        }
      }

      // stop if both lower or upper bounds become infinite
      if( UpInf && LoInf )
        break;
    }

    // check if the computed values are logically correct
    //    if( UpExists && LoExists && !UpInf && !LoInf && UpInfID == LoInfID )
    //      assert( Up >= Lo );

    // deduct from upper bound (if exists)
    if( !UpInf && UpExists )
    {
      // first check if one element is currently unbounded
      if( UpInfID != -1 )
      {
        LAVar * col = columns[UpInfID];
        const Real & a = ( *( row->polynomial.find( UpInfID )->coef ) );
        assert( a != 0 );
        const Delta & b = -1 * Up / a;
        bool a_lt_zero = a < 0;

        if( a_lt_zero && col->U( ) > b )
          col->getDeducedBounds( b, true, deductions, id );
        else if( !a_lt_zero && col->L( ) < b )
          col->getDeducedBounds( b, false, deductions, id );
      }
      // if all are bounded then try to deduce for all of them
      else
      {
        for( LARow::iterator it = row->polynomial.begin( ); it != row->polynomial.end( ); row->polynomial.getNext( it ) )
        {
          const Real & a = ( *( it->coef ) );
          assert( a != 0 );
          LAVar * col = columns[it->key];
          bool a_lt_zero = a < 0;
          const Delta & b = ( a * ( a_lt_zero ? col->L( ) : col->U( ) ) - Up ) / a;

          if( a_lt_zero && col->U( ) >= b )
            col->getDeducedBounds( b, true, deductions, id );
          else if( !a_lt_zero && col->L( ) <= b )
            col->getDeducedBounds( b, false, deductions, id );
        }
      }
    }

    // deduct from lower bound (if exists)
    if( !LoInf && LoExists )
    {
      // first check if one element is currently unbounded
      if( LoInfID != -1 )
      {
        LAVar * col = columns[LoInfID];
        const Real & a = ( *( row->polynomial.find( LoInfID )->coef ) );
        assert( a != 0 );
        const Delta & b = -1 * Lo / a;
        bool a_lt_zero = a < 0;

        if( !a_lt_zero && col->U( ) > b )
          col->getDeducedBounds( b, true, deductions, id );
        else if( a_lt_zero && col->L( ) < b )
          col->getDeducedBounds( b, false, deductions, id );
      }
      // if all are bounded then try to deduce for all of them
      else
      {
        for( LARow::iterator it = row->polynomial.begin( ); it != row->polynomial.end( ); row->polynomial.getNext( it ) )
        {
          const Real & a = ( *( it->coef ) );
          assert( a != 0 );
          LAVar * col = columns[it->key];
          bool a_lt_zero = a < 0;
          const Delta & b = ( a * ( !a_lt_zero ? col->L( ) : col->U( ) ) - Lo ) / a;

          if( !a_lt_zero && col->U( ) >= b )
            col->getDeducedBounds( b, true, deductions, id );
          else if( a_lt_zero && col->L( ) <= b )
            col->getDeducedBounds( b, false, deductions, id );
        }
      }
    }
  }
  touched_rows.clear( );
}

//
// Prints the current state of the solver (terms, bounds, tableau)
//
void LRASolver::print( ostream & out )
{
  out << "Bounds:" << endl;

  // print bounds array size
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
    out << ( *it )->all_bounds.size( ) << "\t";
  out << endl;

  // print the upper bounds
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
    out << ( *it )->U( ) << "\t";
  out << endl;

  // print the lower bounds
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
    out << ( *it )->L( ) << "\t";
  out << endl;

  // print current model values
  out << "Var:" << endl;
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
  {
    out << ( *it ) << "\t";
  }
  out << endl;

  // print current model values
  out << "Model:" << endl;
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
    out << ( *it )->M( ) << "\t";
  out << endl;

  // print the terms IDs
  out << "Tableau:" << endl;
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
    out << ( *it )->ID( ) << "\t";
  out << endl;

  // print the Basic/Nonbasic status of terms
  for( VectorLAVar::iterator it = columns.begin( ); it != columns.end( ); ++it )
    out << ( ( *it )->isBasic( ) ? "B" : "N" ) << "\t";
  out << endl;

  // print the tableau cells (zeros are skipped)
  // iterate over Tableau rows
  for( unsigned i = 0; i < rows.size( ); ++i )
  {
    for( VectorLAVar::iterator it2 = columns.begin( ); it2 != columns.end( ); ++it2 )
    {
      if( rows[i]->polynomial.find( ( *it2 )->ID( ) ) != rows[i]->polynomial.end( ) )
        out << *( rows[i]->polynomial.find( ( *it2 )->ID( ) )->coef );
      out << "\t";
    }
    out << endl;
  }
}

//TODO: -belongsToT not yet implemented
//
// Checks if atom belongs to this theory
//
bool LRASolver::belongsToT( Enode * e )
{
  if( e->isEq( ) )
    return false;
  return true;
}

//
// Detect the appropriate value for symbolic delta and dumps the model into Egraph
//
void LRASolver::computeModel( )
{
  assert( status == SAT );

  Real minDelta( 0 );
  Real maxDelta( 0 );
  Real curDelta( 0 );
  Delta curBound( Delta::ZERO );
  LAVar * col;

  //
  // For all columns check the min/max value for delta
  // Note, it should be always that min > 0 and max < 0
  //
  for( unsigned i = 0; i < columns.size( ); ++i )
  {
    if( columns[i]->skip )
      continue;

    col = columns[i];
    assert( !col->isModelOutOfBounds( ) );

    curDelta = 0;
    curBound = Delta( Delta::ZERO );

    // Check if the lower bound can be used and at least one of delta and real parts are not 0
    if( !col->L( ).isInf( ) 
     && ( col->L( ).D( ) != 0 || col->M( ).D( ) != 0 ) 
     && ( col->L( ).R( ) != 0 || col->M( ).R( ) != 0 ) )
    {
      curBound = col->L( ) - col->M( );

      // if denominator is >0 than use delta for min
      if( curBound.D( ) > 0 )
      {
        curDelta = -( curBound.R( ) / curBound.D( ) );
        if( curDelta != 0 && ( minDelta == 0 || minDelta > curDelta ) )
          minDelta = curDelta;
      }
      // if denominator is <0 than use delta for max
      else if( curBound.D( ) < 0 )
      {
        curDelta = -( curBound.R( ) / curBound.D( ) );
        if( curDelta != 0 && ( maxDelta == 0 || maxDelta < curDelta ) )
          maxDelta = curDelta;
      }
    }
    // Check if the upper bound can be used and at least one of delta and real parts are not 0
    if( !col->U( ).isInf( ) 
     && ( col->U( ).D( ) != 0 || col->M( ).D( ) != 0 ) 
     && ( col->U( ).R( ) != 0 || col->M( ).R( ) != 0 ) )
    {
      curBound = col->M( ) - col->U( );

      // if denominator is >0 than use delta for min
      if( curBound.D( ) > 0 )
      {
        curDelta = -( curBound.R( ) / curBound.D( ) );
        if( curDelta != 0 && ( minDelta == 0 || minDelta > curDelta ) )
          minDelta = curDelta;
      }
      // if denominator is <0 than use delta for max
      else if( curBound.D( ) < 0 )
      {
        curDelta = -( curBound.R( ) / curBound.D( ) );
        if( curDelta != 0 && ( maxDelta == 0 || maxDelta < curDelta ) )
          maxDelta = curDelta;
      }
    }
  }

  // TODO: check if it is it really true :)
  assert( minDelta >= 0 );
  assert( maxDelta <= 0 );
  curDelta = ( minDelta ) / 2;

  // Compute the value for each variable. Delta is taken into account
  for( unsigned i = 0; i < columns.size( ); ++i )
    if( !( columns[i]->skip ) )
      columns[i]->computeModel( curDelta );

  // Compute the value for each variable deleted by Gaussian elimination
  while( !removed_by_GaussianElimination.empty( ) )
  {
    LAVar * x = removed_by_GaussianElimination.back( );

    Real v = 0;
    Real div = 0;

    for( LARow::iterator it = x->polynomial.begin( ); it != x->polynomial.end( ); x->polynomial.getNext( it ) )
    {
      col = columns[it->key];
      if( col != x )
        v += *( it->coef ) * col->e->getComplexValue( );
      else
        div -= *( it->coef );
    }
    assert( div != 0 );
    x->e->setValue( v / div );

    removed_by_GaussianElimination.pop_back( );
  }
}

//
//
//
void LRASolver::addVarToRow( LAVar* s, LAVar* x, Real * p_v )
{

  if( x->isNonbasic( ) )
  {
    LARow::iterator p_it = s->polynomial.find( x->ID( ) );
    if( p_it != s->polynomial.end( ) )
    {
      *( p_it->coef ) += *p_v;
      if( *( p_it->coef ) == 0 )
      {
        numbers_pool.push_back( p_it->coef );
        x->binded_rows.remove( p_it->pos );
        s->polynomial.remove( p_it );
      }
    }
    else
    {
      x->binded_rows.add( s->basicID( ), s->polynomial.add( x->ID( ), x->binded_rows.free_pos( ), p_v ) );
    }
  }
  else
  {
    LARow::iterator it = x->polynomial.begin( );
    for( ; it != x->polynomial.end( ); x->polynomial.getNext( it ) )
    {
      if( x->ID( ) == it->key )
        continue;

      assert( columns[it->key]->isNonbasic( ) );

      Real * tmp_r;

      if( !numbers_pool.empty( ) )
      {
        tmp_r = numbers_pool.back( );
        numbers_pool.pop_back( );
        *tmp_r = Real( *( it->coef ) * ( *p_v ) );
      }
      else
      {
        tmp_r = new Real( *( it->coef ) * ( *p_v ) );
      }
      LARow::iterator p_it = s->polynomial.find( it->key );
      if( p_it != s->polynomial.end( ) )
      {
        *( p_it->coef ) += *tmp_r;
        numbers_pool.push_back( tmp_r );
        if( *( p_it->coef ) == 0 )
        {
          numbers_pool.push_back( p_it->coef );
          columns[it->key]->binded_rows.remove( p_it->pos );
          s->polynomial.remove( p_it );
        }
      }
      else
      {
        columns[it->key]->binded_rows.add( s->basicID( ), s->polynomial.add( it->key, columns[it->key]->binded_rows.free_pos( ), tmp_r ) );
      }
    }
    numbers_pool.push_back( p_v );
  }
}

bool LRASolver::checkIntegersAndSplit( )
{

  assert( config.lra_integer_solver );
  assert( removed_by_GaussianElimination.empty( ) );

  VectorLAVar::const_iterator it = columns.begin( );
  LAVar * x;

  //  unsigned equality_counter=0;
  //  for( ; it != columns.end( ); ++it )
  //    if (( *it )->isEquality())
  //      equality_counter++;
  //
  //  cout << "Equalities in the complete integer check: " << equality_counter << " out of " << columns.size();

  it = columns.begin( );

  for( ; it != columns.end( ); ++it )
  {
    assert( !( *it )->skip );
    if( !( *it )->isModelInteger( ) )
    {
      x = *it;

      // Prepare the variable to store a splitting value
      Real * c = NULL;
      if( !numbers_pool.empty( ) )
      {
        c = numbers_pool.back( );
        numbers_pool.pop_back( );
      }
      else
      {
        c = new Real( 0 );
      }

      // Compute a splitting value
      if( x->M( ).R( ).get_den( ) != 1 )
      {
        if( x->M( ).R( ).get_num( ) < 0 )
          *c = x->M( ).R( ).get_num( ) / x->M( ).R( ).get_den( ) - 1;
        else
          *c = x->M( ).R( ).get_num( ) / x->M( ).R( ).get_den( );
      }
      else
      {
        if( x->M( ).D( ) < 0 )
          *c = x->M( ).R( ) - 1;
        else
          *c = x->M( ).R( );
      }

      // Check if integer splitting is possible for the current variable
      if( *c < x->L( ) && *c + 1 > x->U( ) )
      {
        getConflictingBounds( x, explanation );
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
}

//
// Destructor
//
LRASolver::~LRASolver( )
{
  // Remove slack variables
  while( !columns.empty( ) )
  {
    LAVar * s = columns.back( );
    columns.pop_back( );
    assert( s );
    delete s;
  }
  // Remove numbers
  while( !numbers_pool.empty( ) )
  {
    assert( numbers_pool.back( ) );
    delete numbers_pool.back( );
    numbers_pool.pop_back( );
  }
}

#ifdef PRODUCE_PROOF
//
// Compute interpolants for the conflict
//
Enode * LRASolver::getInterpolants ( logic_t & l )
{
  l = config.logic == QF_LRA || config.logic == QF_UFLRA
  ? QF_LRA
  : QF_LIA;

  assert (explanation.size()>1);

  list<Enode *> in_list;

  ipartitions_t mask = 1;
  mask = ~mask;

  for( unsigned in = 1; in < egraph.getNofPartitions( ); in++ )
  {
    LAExpression interpolant;
    bool delta_flag=false;

    // mask &= ~SETBIT( in );
    clrbit( mask, in );
    for( unsigned i = 0; i < explanation.size( ); i++ )
    {
      icolor_t color = I_UNDEF;
      const ipartitions_t & p = explanation[i]->getIPartitions( );

      if ( isAB( p, mask ) )
      color = I_AB;
      else if ( isAlocal( p, mask ) )
      color = I_A;
      else if ( isBlocal( p, mask ) )
      color = I_B;

      assert( color == I_A
           || color == I_AB
           || color == I_B );

      assert( config.proof_set_inter_algo == 0
           || config.proof_set_inter_algo == 1
           || config.proof_set_inter_algo == 2 );

      // McMillan algo: set AB as B
      if ( config.proof_set_inter_algo == 0
        && color == I_AB )
        color = I_B;
      // McMillan' algo: set AB as a
      else if ( config.proof_set_inter_algo == 2
             && color == I_AB )
        color = I_A;
      // Pudlak algo: who cares
      else if ( config.proof_set_inter_algo == 1
             && color == I_AB )
        color = I_A;

      assert( color == I_A
           || color == I_B );

      // Add the A conflict to the interpolant (multiplied by the coefficient)
      if( color == I_A )
      {
        if ( explanation[i]->getPolarity( ) == l_True )
        {
          interpolant.addExprWithCoeff(LAExpression(explanation[i]), explanationCoefficients[i]);
        }
        else
        {
          interpolant.addExprWithCoeff(LAExpression(explanation[i]), -explanationCoefficients[i]);
          delta_flag=true;
        }
      }
    }

    // TODO:: Why canonization stops the show?
    // intp.canonizeReal();

    // Generate resulting interpolant and push it to the list
    if (interpolant.isTrue() && !delta_flag)
    {
      in_list.push_back(egraph.mkTrue());
    }
    else if (interpolant.isFalse() || ( interpolant.isTrue() && delta_flag ))
    {
      in_list.push_back(egraph.mkFalse());
    }
    else
    {
      if (delta_flag)
        in_list.push_back(egraph.mkLt(egraph.cons(interpolant.toEnode(egraph), egraph.cons(egraph.mkNum("0")))));
      else
        in_list.push_back(egraph.mkLeq(egraph.cons(interpolant.toEnode(egraph), egraph.cons(egraph.mkNum("0")))));
    }
    if ( verbose() > 0 )
    {
      cerr << "Interpolant: " << in_list.back() << endl;
    }

  }
  interpolants = egraph.cons( in_list );
  return interpolants;
}

#endif

