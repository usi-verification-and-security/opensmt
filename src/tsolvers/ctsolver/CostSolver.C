/*********************************************************************
Author: Anders Franzen <pbct@residual.se>

OpenSMT-CT -- Copyright (C) 2010, Anders Franzen

OpenSMT-CT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT-CT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include "CostSolver.h"

#include <iostream>

using namespace std;

#define DEBUG false
#define DEBUG_CONFLICT false
#define ELIM_REDUNDANT true
#define DEBUG_CHECK_STATUS false

namespace {
  /*
   * Output conflict set, used for verbose output
   */
  std::ostream & operator<<( std::ostream & os, std::vector< Enode * > & v )
  {
    os << "[";
    for ( size_t i=0; i<v.size(); ++i )
    {
      Enode * atom = v[ i ];
      assert( atom->getPolarity() != l_Undef );
      if ( atom->getPolarity() == l_False )
      {
        os << "!";
      }
      os << atom;
      if ( i+1 < v.size() )
      {
        os << ", ";
      }
    }
    os << "]";
    return os;
  }
}

CostSolver::CostSolver( const int           i
                      , const char *        n
	              , SMTConfig &         c
	              , Egraph &            e
		      , SStore &            ss
	              , vector< Enode * > & x
	              , vector< Enode * > & d
                      , vector< Enode * > & s )
  : OrdinaryTSolver ( i, n, c, e, ss, x, d, s )
  , conflict_( 0 )
{ 
  //cout << "Allocating Cost solver...\n";
}

CostSolver::~CostSolver( )
{
  //cout << "Freeing Cost solver...\n";
}

lbool CostSolver::inform( Enode * e )  
{ 
  assert( e );
  assert( belongsToT( e ) );
#if DEBUG
  cout << "ct inform " << e << endl;
#endif
  if ( e->isCostIncur() )
  {
    assert( e->getArity() == 3 );
    Enode * args = e->getCdr();
    Enode * var = args->getCar();
    Enode * cost = args->getCdr()->getCar();
#if DEBUG
    cout << "ct inform var = " << var << endl;
    cout << "ct inform cost = " << cost << endl;
#endif
    assert( var->isVar() );
    assert( cost->isConstant() );

    nodemap_t::iterator it = nodemap_.find( var );
    if ( it != nodemap_.end() )
    {
      costfun & fun = *it->second;
      nodemap_[ e ] = &fun;
      add_incur( fun, e, cost );
    }
    else
    {
      costfun * fun = new costfun( var );
#if DEBUG
      cout << "ct new cost fun " << var << endl;
#endif
      nodemap_[ var ] = fun;
      nodemap_[ e ] = fun;
      costfuns_.push_back( fun );
      add_incur( *fun, e, cost );
    }
  }
  if ( e->isCostBound() )
  {
    assert( e->getArity() == 2 );
    Enode * args = e->getCdr();
    Enode * var = args->getCar();

    nodemap_t::iterator it = nodemap_.find( var );
    if ( it != nodemap_.end() )
    {
      costfun & fun = *it->second;
      nodemap_[ var ] = &fun;
      nodemap_[ e ] = &fun;
      add_bound( fun, e );
    }
    else
    {
      costfun * fun = new costfun( var );
#if DEBUG
      cout << "ct new cost fun " << var << endl;
#endif
      nodemap_[ var ] = fun;
      nodemap_[ e ] = fun;
      costfuns_.push_back( fun );
      add_bound( *fun, e );
    }
  }
#if DEBUG
  print_status( cout );
#endif
  return l_Undef;
}

bool CostSolver::assertLit ( Enode * e, bool reason )
{
  (void) reason;
  bool result = assertLitImpl( e );
  return result;
}

bool CostSolver::assertLitImpl( Enode * e )
{
  assert( e );
  assert( belongsToT( e ) );
  assert( e->hasPolarity() );
  assert( e->getPolarity() != l_Undef );
#if DEBUG
  cout << "ct assert " << (e->getPolarity() == l_True ? "" : "!") << e << endl;
#endif

  assert( !conflict_ );

  Enode * atom = e;
  const bool negated = e->getPolarity() == l_False;

  if ( atom->isCostIncur() )
  {
    assert( nodemap_[ atom ] );
    costfun & fun = *nodemap_[ atom ];
#if DEBUG
    print_status( cout, fun );
#endif
    incurnode * node = incurmap_[ atom ];
    if ( node->prev )
    {
      node->prev->next = node->next;
      assert( node->prev->cost <= node->cost );
    }
    if ( node->next )
    {
      node->next->prev = node->prev;
      assert( node->cost <= node->next->cost );
    }
    else
    {
      fun.unassigned.last = node->prev;
    }
    if ( fun.unassigned.head == node )
    {
      fun.unassigned.head = node->next;
    }
    fun.slack -= node->cost;
    fun.assigned.push_back( node );
    if ( negated )
    {
      undo_ops_.push( undo_op( REMOVE_INCUR_NEG, node ) );
      if ( !fun.lowerbound.empty() &&
           get_bound( fun.lowerbound.top() ) > fun.incurred + fun.slack )
      {
        assert( explanation.empty() );
        conflict_ = atom;
        codomain potential = fun.incurred + fun.slack;
        for ( costfun::nodes_t::iterator it = fun.assigned.begin();
              it != fun.assigned.end();
              ++it )
        {
          incurnode * node = *it;
#if ELIM_REDUNDANT
          if ( node->atom->getPolarity() != l_False )
          {
            continue;
          }
          if ( potential + node->cost < get_bound( fun.lowerbound.top() ) )
          {
            potential += node->cost;
            continue;
          }
#endif
          if ( node->atom->getPolarity() == l_False )
          {
            explanation.push_back( node->atom );
          }
        }
        assert( potential < get_bound( fun.lowerbound.top() ) );
        assert( find( explanation.begin(), explanation.end(), conflict_ ) != explanation.end() );
        explanation.push_back( fun.lowerbound.top() );
#if DEBUG_CONFLICT
            cout << " " << explanation << " : " << fun.slack << endl;
            print_status( cout, fun ); cout << endl;
#endif
#if DEBUG
        cout << "conflict found " << conflict_ << endl;
        print_status( cout, fun );
#endif
#if DEBUG_CHECK_STATUS
        check_status();
#endif
        return false;
      }
    }
    else
    {
      fun.incurred += node->cost;
      undo_ops_.push( undo_op( REMOVE_INCUR_POS, node ) );
      if ( !fun.upperbound.empty() &&
           get_bound( fun.upperbound.top() ) <= fun.incurred )
      {
        conflict_ = atom;
        codomain incurred = fun.incurred;
        for ( costfun::nodes_t::iterator it = fun.assigned.begin();
              it != fun.assigned.end();
              ++it )
        {
          incurnode * node = *it;
#if ELIM_REDUNDANT
          if ( node->atom->getPolarity() != l_True )
          {
            continue;
          }
          if ( incurred - node->cost >= get_bound( fun.upperbound.top() ) )
          {
            incurred -= node->cost;
            continue;
          }
#endif
          if ( node->atom->getPolarity() == l_True )
          {
            explanation.push_back( node->atom );
          }
        }
        assert( incurred >= get_bound( fun.upperbound.top() ) );
        assert( find( explanation.begin(), explanation.end(), conflict_ ) != explanation.end() );
        explanation.push_back( fun.upperbound.top() );
#if DEBUG_CONFLICT
            cout << explanation << " : " << fun.slack << endl;
            print_status( cout, fun ); cout << endl;
#endif
#if DEBUG
        cout << "conflict found " << conflict_ << endl;
        print_status( cout, fun );
#endif
#if DEBUG_CHECK_STATUS
        check_status();
#endif
        return false;
      }
    }
  }
  else if ( atom->isCostBound() )
  {
#if DEBUG
    cout << "ct bound asserted " << atom << endl;
#endif
    assert( nodemap_.find( atom ) != nodemap_.end() );
    costfun & fun = *nodemap_[ atom ];
    Enode * args = atom->getCdr();
    Enode * val = args->getCdr( )->getCar( );
    (void)val;
    assert( val->isConstant( ) );
#if DEBUG
    cout << atom->get2nd() << endl;
#endif
    const codomain & value = atom->get2nd()->getValue();
    if ( negated )
    {
#if DEBUG
      cout << "ct bound asserted negatively " << atom << endl;
#endif
      if ( ( !fun.lowerbound.empty() &&
             get_bound( fun.lowerbound.top() ) < value ) ||
           fun.lowerbound.empty() )
      {
#if DEBUG
        cout << "ct new lower bound " << atom << endl;
#endif
        fun.lowerbound.push( atom );
        undo_ops_.push( undo_op( REMOVE_LBOUND, &fun ) );
        if ( fun.incurred + fun.slack < get_bound( fun.lowerbound.top() ) )
        {
          conflict_ = atom;
          codomain potential = fun.incurred + fun.slack;
          for ( costfun::nodes_t::iterator it = fun.assigned.begin();
                it != fun.assigned.end();
                ++it )
          {
            incurnode * node = *it;
#if ELIM_REDUNDANT
            if ( node->atom->getPolarity() != l_False )
            {
              continue;
            }
            if ( potential + node->cost < get_bound( fun.lowerbound.top() ) )
            {
              potential += node->cost;
              continue;
            }
#endif
            if ( node->atom->getPolarity() == l_False )
            {
              explanation.push_back( node->atom );
            }
          }
          assert( find( explanation.begin(), explanation.end(), conflict_ ) == explanation.end() );
          explanation.push_back( conflict_ );
          assert( potential < get_bound( fun.lowerbound.top() ) );
          assert( find( explanation.begin(), explanation.end(), conflict_ ) != explanation.end() );
#if DEBUG_CONFLICT
            cout << explanation << " : " << fun.slack << endl;
            print_status( cout, fun ); cout << endl;
#endif
#if DEBUG
          cout << "conflict found " << conflict_ << endl;
          print_status( cout, fun );
#endif
#if DEBUG_CHECK_STATUS
          check_status();
#endif
          return false;
        }
      }
    }
    else
    {
#if DEBUG
      cout << "ct bound asserted positively " << atom << endl;
#endif
      if ( ( !fun.upperbound.empty() &&
             get_bound( fun.upperbound.top() ) > value ) ||
           fun.upperbound.empty() )
      {
#if DEBUG
        cout << "ct new upper bound " << atom << endl;
#endif
        fun.upperbound.push( atom );
        undo_ops_.push( undo_op( REMOVE_UBOUND, &fun ) );
        if ( fun.incurred >= get_bound( fun.upperbound.top() ) )
        {
          conflict_ = atom;
          codomain incurred = fun.incurred;
          for ( costfun::nodes_t::iterator it = fun.assigned.begin();
                it != fun.assigned.end();
                ++it )
          {
            incurnode * node = *it;
#if ELIM_REDUNDANT
            if ( node->atom->getPolarity() != l_True )
            {
              continue;
            }
            if ( incurred - node->cost >= get_bound( fun.upperbound.top() ) )
            {
              incurred -= node->cost;
              continue;
            }
#endif
            if ( node->atom->getPolarity() == l_True )
            {
              explanation.push_back( node->atom );
            }
          }
          assert( find( explanation.begin(), explanation.end(), conflict_ ) == explanation.end() );
          assert( incurred >= get_bound( fun.upperbound.top() ) );
          explanation.push_back( conflict_ );
          assert( find( explanation.begin(), explanation.end(), conflict_ ) != explanation.end() );
#if DEBUG_CONFLICT
            cout << " " << explanation << " : " << fun.slack << endl;
            print_status( cout, fun ); cout << endl;
#endif
#if DEBUG
          cout << "conflict found " << conflict_ << endl;
          print_status( cout, fun );
#endif
#if DEBUG_CHECK_STATUS
          check_status();
#endif
          return false;
        }
      }
    }
    if ( !fun.lowerbound.empty() && !fun.upperbound.empty() &&
         get_bound( fun.lowerbound.top() ) >= get_bound( fun.upperbound.top() ) )
    {
      conflict_ = atom;
      explanation.push_back( fun.lowerbound.top() );
      explanation.push_back( fun.upperbound.top() );
#if DEBUG_CONFLICT
            cout << " " << explanation << " : " << fun.slack << endl;
            print_status( cout, fun ); cout << endl;
#endif
#if DEBUG
      cout << "conflict found " << conflict_ << endl;
      print_status( cout, fun );
#endif
#if DEBUG_CHECK_STATUS
      check_status();
#endif
      return false;
    }
  }
  else
  {
#if DEBUG
    cout << "ct unrecognized " << atom << endl;
#endif
  }

#if 1
  {
    // Deduction
    costfun & fun = *nodemap_[ atom ];
    if ( !fun.upperbound.empty() &&
         fun.lowerbound.empty() &&
         fun.unassigned.last &&
         get_bound( fun.upperbound.top() ) <= fun.unassigned.last->cost + fun.incurred  &&
         !fun.unassigned.last->atom->isDeduced() )
    {
#if DEBUG
      cout << "deducing !" << fun.unassigned.last->atom << endl;
#endif
      fun.unassigned.last->atom->setDeduced( l_False, id );
      deductions.push_back( fun.unassigned.last->atom );
    }
    else if ( !fun.lowerbound.empty() &&
         fun.upperbound.empty() &&
         fun.unassigned.last &&
         get_bound( fun.lowerbound.top() ) > fun.incurred + fun.slack - fun.unassigned.last->cost &&
         !fun.unassigned.last->atom->isDeduced() )
    {
#if DEBUG
      cout << "deducing " << fun.unassigned.last->atom << endl;
#endif
      fun.unassigned.last->atom->setDeduced( l_True, id );
      deductions.push_back( fun.unassigned.last->atom );
    }
    else if ( !fun.upperbound.empty() &&
              !fun.lowerbound.empty() &&
              fun.unassigned.last &&
              get_bound( fun.lowerbound.top() ) +1 == get_bound( fun.upperbound.top() ) )
    {
      if ( fun.unassigned.last->cost == fun.slack &&
           fun.incurred + fun.unassigned.last->cost ==
           get_bound( fun.lowerbound.top() ) &&
           fun.incurred + fun.slack - fun.unassigned.last->cost <
           get_bound( fun.lowerbound.top() ) )
      {
#if DEBUG
      cout << "deducing " << fun.unassigned.last->atom << endl;
      print_status( cout, fun );
#endif
        fun.unassigned.last->atom->setDeduced( l_True, 0 );
        deductions.push_back( fun.unassigned.last->atom );
      }
    }
  }
#endif

#if DEBUG_CHECK_STATUS
  check_status();
#endif
  return true;
}

void CostSolver::pushBacktrackPoint ( )
{
  backtrack_points_.push( undo_ops_.size() );
}

void CostSolver::popBacktrackPoint ( )
{
  const size_t size = backtrack_points_.top();
  backtrack_points_.pop();
  for ( ; undo_ops_.size() > size; undo_ops_.pop() )
  {
    undo_op op = undo_ops_.top();
    switch ( op.opcode )
    {
      case REMOVE_LBOUND:
#if DEBUG
        cout << "ct remove lower bound " << op.fun->lowerbound.top() << endl;
#endif
        if ( conflict_ == op.fun->lowerbound.top() )
        {
          conflict_ = 0;
        }
        op.fun->lowerbound.pop();
        break;
      case REMOVE_UBOUND:
#if DEBUG
        cout << "ct remove upper bound " << op.fun->upperbound.top() << endl;
#endif
        if ( conflict_ == op.fun->upperbound.top() )
        {
          conflict_ = 0;
        }
        op.fun->upperbound.pop();
        break;
      case REMOVE_INCUR_POS:
        {
#if DEBUG
          cout << "ct remove " << op.node->atom << endl;
#endif
          incurnode * node = op.node;
          if ( node->prev )
          {
            node->prev->next = node;
#if DEBUG
            cout << "ct inserted after" << node->prev->atom << endl;
            cout << "ct inserted head" << node->fun.unassigned.head->atom << endl;
#endif
            assert( node->prev->cost <= node->cost );
          }
          else
          {
            node->fun.unassigned.head = node;
          }
          if ( node->next )
          {
            node->next->prev = node;
            assert( node->cost <= node->next->cost );
          }
          else
          {
            node->fun.unassigned.last = node;
          }
          assert( node == node->fun.assigned.back() );
          node->fun.assigned.pop_back();
          node->fun.incurred -= node->cost;
          node->fun.slack += node->cost;
          if ( conflict_ == node->atom )
          {
            conflict_ = 0;
          }
        }
        break;
      case REMOVE_INCUR_NEG:
        {
#if DEBUG
          cout << "ct remove !" << op.node->atom << endl;
#endif
          incurnode * node = op.node;
          if ( node->prev )
          {
            node->prev->next = node;
            assert( node->prev->cost <= node->cost );
          }
          else
          {
            node->fun.unassigned.head = node;
          }
          if ( node->next )
          {
            node->next->prev = node;
            assert( node->cost <= node->next->cost );
          }
          else
          {
            node->fun.unassigned.last = node;
          }
          assert( node == node->fun.assigned.back() );
          op.node->fun.assigned.pop_back();
          op.node->fun.slack += node->cost;
          if ( conflict_ == node->atom )
          {
            conflict_ = 0;
          }
        }
        break;
    }
  }
}

bool CostSolver::check( bool complete )    
{ 
  (void)complete;
  // Here check for consistency
  if ( complete )
  {
    if ( conflict_ )
    {
#if DEBUG
      cout << "ct check found conflict " << conflict_ << endl;
#endif
    }
    else
    {
#if DEBUG
      cout << "ct check found model" << endl;
#endif
    }
  }
  return !conflict_;
}

bool CostSolver::belongsToT( Enode * e )
{
  assert( e );
  return e->isCostIncur() || e->isCostBound();
}

void CostSolver::computeModel( )
{
#if DEBUG
  cout << "ct computing model\n";
  print_status( cout );
#endif
  for ( costfuns_t::iterator it = costfuns_.begin();
        it != costfuns_.end();
        ++it )
  {
    costfun & fun = **it;
#if DEBUG
    cout << "ct ";
    cout << fun.variable << " := ";
    cout << "[" << fun.incurred << " : " << fun.slack << "]" << endl;
#endif
    fun.variable->setValue( fun.incurred );
  }
}

void CostSolver::add_incur( costfun & fun, Enode * atom, Enode * cost )
{
  assert( atom->isCostIncur() );
  assert( cost->isConstant() );
  assert( fun.incurred == 0 );
#if DEBUG
  cout << "ct add_incur cost " << cost << endl;
  print_status( cout, fun );
#endif
  const Real & value = cost->getValue();
  incurlist & list = fun.unassigned;
  if ( !list.head )
  {
    incurnode * node = new incurnode( fun, atom, value );
    list.head = node;
    list.last = node;
    incurmap_[ atom ] = node;
    assert( !node->next );
    assert( !node->prev );
  }
  else
  {
    incurnode * cur = list.head;
    for ( ;
          cur->cost < value && cur->next;
          cur = cur->next ) { }
    incurnode * node = new incurnode( fun, atom, value );
    if ( cur->cost > value )
    {
#if DEBUG
      cout << "inserting before " << cur->atom << endl;
#endif
      node->next = cur;
      node->prev = cur->prev;
      if ( cur->prev )
      {
        cur->prev->next = node;
      }
      cur->prev = node;
    }
    else
    {
#if DEBUG
      cout << "inserting after " << cur->atom << endl;
#endif
      node->next = cur->next;
      cur->next = node;
      node->prev = cur;
      if ( node->next )
      {
        node->next->prev = node;
      }
    }
    if ( !node->prev )
    {
      list.head = node;
    }
    if ( !node->next )
    {
      list.last = node;
    }
    incurmap_[ atom ] = node;
  }
  fun.slack += value;
}

void CostSolver::add_bound( costfun &, Enode * atom )
{
  (void)atom;
  assert( atom->isCostBound() );
}

const CostSolver::codomain & CostSolver::get_bound( Enode * bound )
{
  assert( bound->isCostBound() );
  return bound->get2nd()->getValue();
}

const CostSolver::codomain & CostSolver::get_incurred( Enode * incur )
{
  assert( incur->isCostIncur() );
  return incur->get2nd()->getCar()->getValue();
}

void CostSolver::print_status( std::ostream & os )
{
  for ( costfuns_t::iterator it = costfuns_.begin();
        it != costfuns_.end();
        ++it )
  {
    costfun & fun = **it;
    print_status( os, fun );
  }
  if ( conflict_ )
  {
    os << "ct conflict " << conflict_ << endl;
  }
}

void CostSolver::check_status()
{
#ifndef NDEBUG
  for ( costfuns_t::iterator it = costfuns_.begin();
        it != costfuns_.end();
        ++it )
  {
    costfun & fun = **it;
    codomain slack = 0;
    for ( incurnode * n=fun.unassigned.head; n; n=n->next )
    {
      assert( !n->atom->hasPolarity() );
      if ( n->next )
      {
        assert( n != n->next );
        if ( n->cost > n->next->cost )
        {
          cout << n->cost << " > " << n->next->cost << endl;
        }
        assert( n->cost <= n->next->cost );
        assert( n->next->prev == n );
      }
      if ( n->prev )
      {
        assert( n->prev != n );
        assert( n->prev->next == n );
      }
      slack += get_incurred( n->atom );
    }
    assert( slack == fun.slack );
    {
      codomain incurred = 0;
      for ( costfun::nodes_t::iterator it = fun.assigned.begin();
            it != fun.assigned.end();
            ++it )
      {
        incurnode * node = *it;
        assert( node->atom->hasPolarity() );
        if ( node->atom->getPolarity() == l_True )
        {
          incurred += get_incurred( node->atom );
        }
      }
      if ( fun.incurred != incurred )
      {
        if ( conflict_ )
        {
          cout << "conflict = " << conflict_ << endl;
        }
        cout << "incurred = " << incurred << endl;
        print_status( cout, fun );
      }
      assert( fun.incurred == incurred );
    }
  }
  if ( conflict_ )
  {
    cout << "ct conflict " << conflict_ << endl;
    costfun & fun = *nodemap_.find( conflict_ )->second;
    codomain incurred = 0;
    Enode * upper_bound = 0;
    Enode * lower_bound = 0;
    for ( vector<Enode*>::iterator it = explanation.begin();
          it != explanation.end();
          ++it )
    {
      Enode * atom = *it;
      assert( atom->hasPolarity() );
      if ( atom->isCostIncur() )
      {
        if ( atom->getPolarity() == l_True )
        {
          incurred += get_incurred( atom );
        }
      }
      if ( atom->isCostBound() )
      {
        if ( atom->getPolarity() == l_True )
        {
          assert( !upper_bound );
          upper_bound = atom;
        }
        else
        {
          assert( !lower_bound );
          assert( atom->getPolarity() == l_False );
          lower_bound = atom;
        }
      }
    }
    if ( !fun.lowerbound.empty() && fun.upperbound.empty() )
    {
      assert( fun.incurred + fun.slack < get_bound( fun.lowerbound.top() ) );
    }
    if ( fun.lowerbound.empty() && !fun.upperbound.empty() )
    {
      assert( fun.incurred >= get_bound( fun.upperbound.top() ) );
      assert( incurred >= get_bound( upper_bound ) );
    }
  }
#endif
}

void CostSolver::print_status( std::ostream & os, costfun & fun )
{
    os << "ct ";
    os << fun.variable << ": ";
    os << "[" << fun.incurred << ":" << fun.slack << "]";
    os << " [";
    if ( fun.lowerbound.empty() )
    {
      os << "_";
    }
    else
    {
      os << fun.lowerbound.top();
    }
    os << ":";
    if ( fun.upperbound.empty() )
    {
      os << "_";
    }
    else
    {
      os << fun.upperbound.top();
    }
    os << "]";
#ifndef NDEBUG
    for ( incurnode * n=fun.unassigned.head; n; n=n->next )
    {
      if ( n->next )
      {
        if ( n->cost > n->next->cost )
        {
          cout << n->cost << " > " << n->next->cost << endl;
        }
        assert( n->cost <= n->next->cost );
        assert( n->next->prev == n );
      }
      if ( n->prev )
      {
        assert( n->prev->next == n );
      }
    }
#endif
#if 1
    os << " unassigned ";
    for ( incurnode * n=fun.unassigned.head; n; n=n->next )
    {
      os << n->atom << " ";
      assert( n != n->next );
    }
    os << " assigned ";
    for ( costfun::nodes_t::iterator kt = fun.assigned.begin();
          kt != fun.assigned.end();
          ++kt )
    {
      if ( (*kt)->atom->getPolarity() == l_False )
      {
        os << "!";
      }
      os << (*kt)->atom << " ";
    }
    os << endl;
#endif
}
