/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>
        Aliaksei Tsitovich <aliaksei.tsitovich@gmail.com>

OpenSMT2 -- copyright (C) 2012 - 2015, Antti Hyvarinen
OpenSMT -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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

#include "LA.h"

//
// Scan the enode and prepare the polynome
// Notice that it won't work on non-linear
// polynomes -- "unpredictable" result
//
void LAExpression::initialize( PTRef e, bool do_canonize )
{
  assert( logic.isNumEq(e) || logic.isNumLeq(e) );
  integers = false;

  vector< PTRef > curr_term;
  vector< opensmt::Real >    curr_const;

  PTRef lhs = logic.getPterm(e)[0];
  PTRef rhs = logic.getPterm(e)[1];
  curr_term .push_back( lhs );
  curr_const.push_back( 1 );
  curr_term .push_back( rhs );
  curr_const.push_back( -1 );

  while ( !curr_term.empty( ) )
  {
    PTRef t = curr_term.back( );
    curr_term.pop_back( );
    opensmt::Real c = curr_const.back( );
    curr_const.pop_back( );
    //
    // Only 3 cases are allowed
    //
    // If it is plus, enqueue the arguments with same constant
    //
    if ( logic.isNumPlus(t) ) {
      const Pterm& term = logic.getPterm(t);
      for (int i = 0; i < term.size(); i++) {
        PTRef arg = term[i];
        curr_term .push_back( arg );
        curr_const.push_back( c );
      }
    }
    //
    // If it is times, then one side must be constant, other
    // is enqueued with a new constant
    //
    else if ( logic.isNumTimes(t) ) {
        const Pterm& term = logic.getPterm(t);
        assert( term.size() == 2 );
        PTRef x = term[0];
        PTRef y = term[1];
        assert(logic.isConstant(x) || logic.isConstant(y));
        if (logic.isConstant(y)) {
            PTRef tmp = y;
            y = x;
            x = tmp;
        }

        opensmt::Real new_c = logic.getNumConst(x);
        new_c = new_c * c;
        curr_term .push_back( y );
        curr_const.push_back( std::move(new_c) );
    }
    //
    // Otherwise it is a variable, Ite, UF or constant
    //
    else
    {
      assert(logic.isNumVarOrIte(t) || logic.isConstant(t) || logic.isUF(t));
      if ( logic.isConstant(t) ) {
        const opensmt::Real tval = logic.getNumConst(t);
        polynome[ PTRef_Undef ] += tval * c;
      } else {
        if (logic.hasSortNum(t))
          integers = true;

        polynome_t::iterator it = polynome.find( t );
        if ( it != polynome.end( ) ) {
          it->second += c;
          if ( it->first != PTRef_Undef && it->second == 0 )
            polynome.erase( it );
        } else
          polynome[ t ] = c;
      }
    }
  }

  if ( polynome.find( PTRef_Undef ) == polynome.end( ) )
    polynome[ PTRef_Undef ] = 0;
  //
  // Canonize
  //
    if(do_canonize){
        canonize( );
    }
}

//PTRef LAExpression::getPTRefConstant()
//{
//    return logic.mkConst(getRealConstant());
//}

opensmt::Real
LAExpression::getRealConstant()
{
  assert( polynome.find( PTRef_Undef ) != polynome.end( ) );
  assert( polynome.size( ) > 0 );
  //
  // There is at least one variable
  //
  for ( polynome_t::iterator it = polynome.begin( )
      ; it != polynome.end( )
      ; it ++ )
  {
    if ( it->first == PTRef_Undef )
      return it->second;
  }
  throw std::logic_error("No constant in a polynomial");
}

PTRef LAExpression::getPTRefNonConstant()
{
  assert( polynome.find( PTRef_Undef ) != polynome.end( ) );
  assert( polynome.size( ) > 0 );
  //
  // There is at least one variable
  //
  vec<PTRef> sum_list;
  opensmt::Real constant = 0;
  for ( polynome_t::iterator it = polynome.begin( )
      ; it != polynome.end( )
      ; it ++ )
  {
    if ( it->first == PTRef_Undef )
      constant = it->second;
    else
    {
      char* msg;
      PTRef coeff = logic.mkConst(it->second);
      PTRef vv = it->first;
      vec<PTRef> term;
      term.push(coeff);
      term.push(vv);
      sum_list.push( logic.mkNumTimes(term, &msg) );
    }
  }
  if ( sum_list.size() == 0)
  {
    sum_list.push(logic.getTerm_NumZero());
  }
  PTRef poly = logic.mkNumPlus(sum_list);
  return poly;
}

PTRef LAExpression::toPTRef() const
{
  assert( polynome.find( PTRef_Undef ) != polynome.end( ) );
  assert( polynome.size( ) > 0 );
  //
  // There is at least one variable
  //
  vec<PTRef> sum_list;
  opensmt::Real constant = 0;
  for ( auto it = polynome.begin( )
      ; it != polynome.end( )
      ; it ++ )
  {
    if ( it->first == PTRef_Undef )
      constant = it->second;
    else
    {
      char* msg;
      PTRef coeff = logic.mkConst(it->second);
      PTRef vv = it->first;
      vec<PTRef> term;
      term.push(coeff);
      term.push(vv);
      sum_list.push( logic.mkNumTimes(term, &msg) );
    }
  }
  if ( sum_list.size() == 0)
  {
    sum_list.push(logic.getTerm_NumZero());
  }
  //
  // Return in the form ax + by + ... = -c
  //
  if ( r == EQ || r == LEQ )
  {
    PTRef poly = logic.mkNumPlus(sum_list);
    constant = -constant;
    PTRef c = logic.mkConst(constant);
    if ( r == EQ ) {
        vec<PTRef> args;
        args.push(poly);
        args.push(c);
        return logic.mkEq(args);
    }
    else {
       return logic.mkNumLeq(poly, c);
    }
  }
  //
  // Return in the form ax + by + ... + c
  //
  assert( r == UNDEF );
  sum_list.push(logic.mkConst(constant));
  PTRef poly = logic.mkNumPlus(sum_list);

  return poly;
}
//
// Print
//
void LAExpression::print( ostream & os ) const
{
  assert( polynome.find( PTRef_Undef ) != polynome.end( ) );
  assert( polynome.size( ) > 0 );
  if ( r == EQ )
    os << "(=";
  else if ( r == LEQ )
    os << "(<=";
  opensmt::Real constant = 0;
  if ( polynome.size( ) == 1 )
    os << " " << polynome.at(PTRef_Undef);
  else
  {
    //
    // There is at least one variable
    //
    os << " (+";
    for ( auto it = polynome.begin( )
	; it != polynome.end( )
	; it ++ )
    {
      if ( it->first == PTRef_Undef )
	constant = -it->second;
      else
	os << " (* " << it->second << " " << logic.printTerm(it->first) << ")";
    }
    os << ")";
  }
  if ( r == EQ || r == LEQ )
    os << " " << constant << ")";
  os << '\n';
}
//
// Produce a substitution
//
std::pair<PTRef, PTRef> LAExpression::getSubst() {
    assert(polynome.find(PTRef_Undef) != polynome.end());
    assert(r != UNDEF);
    return getSubstReal();
}

std::pair<PTRef, PTRef> LAExpression::getSubstReal() {
    if (polynome.size() == 1) {
        assert(polynome.find(PTRef_Undef) != polynome.end());
        return std::make_pair(PTRef_Undef, PTRef_Undef);
    }
    // There is at least one variable
    // Solve w.r.t. first variable
    solve();
    vec<PTRef> sum_list;
    opensmt::Real constant = 0;
    PTRef var = PTRef_Undef;
    for (auto rit = polynome.rbegin(); rit != polynome.rend(); ++rit) {
        if (rit->first == PTRef_Undef)
            constant = -rit->second;
        else {
            if (var == PTRef_Undef) {
                var = rit->first;
                assert(rit->second == 1);
            } else {
                opensmt::Real coeff = -rit->second;
                PTRef c = logic.mkConst(coeff);
                PTRef vv = rit->first;
                sum_list.push(logic.mkNumTimes(c, vv));
            }
        }
    }
    sum_list.push(logic.mkConst(constant));
    PTRef poly = logic.mkNumPlus(sum_list);
    return std::make_pair(var, poly);
}
//
// Solve w.r.t. first variable
// ex.
//
// 3*x + 2*y -1*z + 5 = 0
//
// 1*x + 2/3*y - 1/3*z + 5/3 = 0
//
// it modifies the polynome internally
//
PTRef LAExpression::solve()
{
    assert(r == EQ);
    assert(polynome.find(PTRef_Undef) != polynome.end());
    if (polynome.size() == 1) {
        return PTRef_Undef;
    }
    // Get first useful variable
    // MB: We start from the end to pick a PTRef with highest ID. This is important in the presence if ITEs
    // to prevent a substitution of the form "x -> ite(b,x,y)" which would cause cycle in the substitution loop
    auto rit = polynome.rbegin();
    if (rit->first == PTRef_Undef) { ++rit; }
    PTRef var = rit->first;
    const opensmt::Real coeff = rit->second;
    // Divide polynome by coeff
    for (auto & term : polynome) {
        term.second /= coeff;
    }
    assert(polynome.at(var) == 1);
    return var;
}
//
// Canonize w.r.t. first variable
// ex.
//
// 3*x + 2*y -1*z + 5 = 0
//
// 1*x + 2/3*y - 1/3*z + 5/3 = 0
//
// it modifies the polynome internally
//
void
LAExpression::canonize( )
{
    assert(polynome.find(PTRef_Undef) != polynome.end());
    canonizeReal();
}

void
LAExpression::canonizeReal() {
    if (polynome.size() == 1) {
        assert(polynome.find(PTRef_Undef) != polynome.end());
        return;
    }
    // Get first useful variable
    auto rit = polynome.rbegin();
    if (rit->first == PTRef_Undef) { ++rit; }
    opensmt::Real coeff;
    if (r == LEQ) {
        coeff = (rit->second > 0 ? rit->second : opensmt::Real(-rit->second));
    } else {
         coeff = rit->second;
    }
    for (auto & term : polynome) {
        term.second /= coeff;
    }
    assert(isCanonized());
}

void LAExpression::addExprWithCoeff(const LAExpression &a, const opensmt::Real &coeff) {
    // Iterate over expression to add
    for (auto it = a.polynome.begin(); it != a.polynome.end(); ++it) {
        auto it2 = polynome.find(it->first);
        if (it2 != polynome.end()) {
            it2->second += coeff * it->second;
            if (it2->first != PTRef_Undef && it2->second == 0) {
                polynome.erase(it2);
            }
        } else {
            polynome.insert(std::make_pair(it->first, coeff * it->second));
        }
    }
}
