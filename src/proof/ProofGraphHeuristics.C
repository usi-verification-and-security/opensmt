/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

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

#include "ProofGraph.h"

#ifdef PRODUCE_PROOF

bool ProofGraph::trivialApplicationCriterion( RuleContext & ra
                                            , bool duplAllowed )
{
  // FIXME: useless parameters
  (void)ra;
  (void)duplAllowed;
  return true;
}

// Input: a context, a flag to enable clauses duplication
// Assume the proof is a tree
// Output: true if A rule should be applied
bool ProofGraph::ARulesReductionApplicationCriterionTree( RuleContext & ra
                                                        , bool duplAllowed )
{
  // FIXME: useless parameter
  (void)duplAllowed;
	assert(graph[ra.cw]->res.size()==1);
	//Applies A rule if this leads to a new redundancy along paths from v to leaves
	//Assuming no redundancies are present, only useful possibility is for w pivot to be in v3 subtree
	//In fact both A1 and A2 create a new path v->w'->v3 with both pivots

	if(ra.type==rA1 || ra.type==rA1B) return false;

	Var pivot=graph[ra.cw]->pivot;
	bool pivot_found;

	pivot_found=findPivotInSubproof(pivot, ra.cv3);
	if(pivot_found) return true; else return false;
}

//Input: a context, a flag to enable clauses duplication
//Output: true if A rule should be applied
//Given a set of light variables to be pushed up and a rule context, returns true if t1 is light and t0 heavy
//(which means that we are pushing up t1), false otherwise
bool ProofGraph::ARulesInterpolationApplicationCriterionWeak(RuleContext& ra, bool duplAllowed)
{
	Var t0=graph[ra.cw]->pivot;
	Var t1=graph[ra.cv]->pivot;
	bool t0Light=(light_vars.find(t0)!=light_vars.end());
	bool t1Light=(light_vars.find(t1)!=light_vars.end());
	bool dupl=(graph[ra.cw]->res.size()>1);
	rul_type t=ra.type;

	if((dupl && duplAllowed) || (!dupl))
	{
		//Conditions added 30/07

		//Try to exploit A1undo in case pivots same partition
		if(t0Light && t1Light && t==rA1undo) return true;
		if(!t0Light && !t1Light && t==rA1undo) return true;

		//Try to delay A1s
		if(!duplAllowed && (t==rA1 || t==rA1B)) return false;

		if(!t0Light && t1Light) return true;
	}
	return false;
}

//Input: a context, a flag to enable clauses duplication
//Output: true if A rule should be applied
//Given a set of light variables to be pushed up and a rule context, returns true if t1 is light and t0 heavy
//or if both t0 and t1 are light/heavy (which means that we are pushing up t1), false otherwise
//NB This criterion is useful for B2 application, can cause loop for A2
bool ProofGraph::ARulesInterpolationApplicationCriterionStrong(RuleContext& ra, bool duplAllowed)
{
	Var t0=graph[ra.cw]->pivot;
	Var t1=graph[ra.cv]->pivot;
	bool t0Light=(light_vars.find(t0)!=light_vars.end());
	bool t1Light=(light_vars.find(t1)!=light_vars.end());
	bool dupl=(graph[ra.cw]->res.size()>1);

	if((dupl && duplAllowed) || (!dupl))
	{
		if((!t0Light && t1Light) || (t0Light && t1Light) || (!t0Light && !t1Light)) return true;
	}
	return false;

}

//Input: a context for a swap rule
//Output: true if rule application is allowed
bool ProofGraph::allowSwapRule(RuleContext& ra, bool duplAllowed)
{
	rul_type t=ra.type;
	bool dupl=(graph[ra.cw]->res.size()>1);

	if((dupl && duplAllowed) || (!dupl))
	{
		//Always allow rB2k
		if(t==rB2k) return true;
		//Allow A1 undo if no duplications
		if(t==rA1undo && !dupl) return true;
		//Allow A2 if no duplications
		if(t==rA2B && !dupl) return true;
		if((t==rA2 || t==rA2u) && !dupl) return true;
		//if(t==rA1B && !dupl) return true;
	}
	//Don't allow the rest
	return false;
}

// Input: a context for a cut rule
// Output: true if rule application is allowed
bool ProofGraph::allowCutRule(RuleContext& ra, bool duplAllowed)
{
  // FIXME: useless parameters
  (void)ra;
  (void)duplAllowed;
	return true;
}

//Input: two rule contexts, methods to determine applicability of rules, flags for allowing node duplications
//Output: 0,1,2 if no context, first context, second context is chosen for application
short ProofGraph::handleRuleApplication(RuleContext& ra1,RuleContext& ra2,
		bool(ProofGraph::*allowSwap)(RuleContext& ra, bool duplAll),bool(ProofGraph::*allowCut)(RuleContext& ra, bool duplAll),
		bool dupl_allowed_swap, bool dupl_allowed_cut)
{
	short chosen=0;
	//Randomize application of rules
	if( !additionalRandomization() || rand()%2==0 )
	{
		//Decide which one to apply, if any
		short which=contextChoiceCriterion(ra1,ra2,allowSwap,allowCut,dupl_allowed_swap,dupl_allowed_cut);
		if(which!=0)
		{
			//Can add further randomness for application swap rules
			if( (which==1 && isSwapRule( ra1.type )) || (which==2 && isSwapRule( ra2.type )) )
			{
				if( !randomApplicationSwap() || rand()%2==0 )
					chosen=which;
			}
			//Can add further randomness for application cut rules
			else if( (which==1 && isCutRule( ra1.type )) || (which==2 && isCutRule( ra2.type )) )
			{
				if( !randomApplicationCut() || rand()%2==0 )
					chosen=which;
			}
			else chosen=which;
		}
	}
	return chosen;
}


//Input: a pair of left/right contexts, a heuristic criterion for A rules application, a flag to allow clauses duplication
//Output: 0,1,2 to apply no rule, rule1, rule2
short ProofGraph::contextChoiceCriterion(RuleContext& ra1,RuleContext& ra2,
		bool(ProofGraph::*allowSwap)(RuleContext& ra, bool duplAll),bool(ProofGraph::*allowCut)(RuleContext& ra, bool duplAll),
		bool duplAllowedSwap, bool duplAllowedCut)
{
	short choose=-1;
	rul_type t1=ra1.type;
	rul_type t2=ra2.type;
	bool all1,all2;
	bool is1cut=isCutRule(t1);
	bool is2cut=isCutRule(t2);
	bool is1swap=isSwapRule(t1);
	bool is2swap=isSwapRule(t2);

	//rA1,rA2,rA2u,rA1B,rA2B,rA1undo,rB2k,rB3,rB1,rB2

	//Both not applicable
	if(t1==rNO && t2==rNO) choose=0;

	//First not applicable
	else if(t1==rNO && t2!=rNO)
	{
		if(is2swap)
		{
			//Check criterion
			if((*this.*allowSwap)(ra2,duplAllowedSwap))
				choose=2;
			else choose=0;
		}
		else if(is2cut)
		{
			//Check criterion
			if((*this.*allowCut)(ra2,duplAllowedCut))
				choose=2;
			else choose=0;
		}
		else
			assert(false);
	}
	//Second not applicable
	else if(t1!=rNO && t2==rNO)
	{
		//Check ordering criterion
		if(is1swap)
		{
			if((*this.*allowSwap)(ra1,duplAllowedSwap))
				choose=1;
			else choose=0;
		}
		else if(is1cut)
		{
			if((*this.*allowCut)(ra1,duplAllowedCut))
				choose=1;
			else choose=0;
		}
		else
			assert(false);
	}
	if(choose!=-1) return choose;

	//Both applicable
	bool dupl1=graph[ra1.cw]->res.size() > 1;
	bool dupl2=graph[ra2.cw]->res.size() > 1;

	//Case one cuts, the other swaps: privilege cut
	if(is1cut && is2swap)
		choose=1;
	else if(is2cut && is1swap)
		choose=2;
	//Case both cut
	else if(is1cut && is2cut)
	{
		//Privilege the one not duplicating
		if(dupl1 && !dupl2) choose=2;
		else if(!dupl1 && dupl2) choose=1;
		//Privilege B3 over B1 and B2
		else if(t1==rB3 && t2!=rB3) choose=1;
		else if(t1!=rB3 && t2==rB3) choose=2;
		//Break ties randomly
		else { if(rand()%2==0)choose=1; else choose=2; }
	}
	//Case both swap
	else if(is2swap && is1swap)
	{
		all1=(*this.*allowSwap)(ra1,duplAllowedSwap);
		all2=(*this.*allowSwap)(ra2,duplAllowedSwap);
		//At least one not allowed
		if(all1 && !all2) choose=1;
		else if(!all1 && all2) choose=2;
		else if(!all1 && !all2) choose=0;
		//Both allowed
		else
		{
			//Privilege the one not duplicating
			if(dupl1 && !dupl2) choose=2;
			else if(!dupl1 && dupl2) choose=1;
			//Privilege A1undo, then B2k, then A2 over A1
			else if(t1==rA1undo && t2!=rA1undo) choose=1;
			else if(t1!=rA1undo && t2==rA1undo) choose=2;
			else if(t1==rB2k && t2!=rB2k) choose=1;
			else if(t1!=rB2k && t2==rB2k) choose=2;
			else if((t1==rA2 || t1==rA2u || t1==rA2B) && (t2==rA1 || t2==rA1B)) choose=1;
			else if((t2==rA2 || t2==rA2u || t2==rA2B) && (t1==rA1 || t1==rA1B)) choose=2;
			//Privilege A2B over A2 and A1B over A1
			else if((t1==rA2B && (t2==rA2 || t2==rA2u)) || (t1==rA1B && t2==rA1)) choose=1;
			else if((t2==rA2B && (t1==rA2 || t1==rA2u)) || (t2==rA1B && t1==rA1)) choose=2;
			//Break ties
			else
			{
				//TODO randomness seems to work better!
				if(rand()%2==0)choose=1; else choose=2;

				/*				//Give priority to pushing down leaves...can help linearizing proof?
				bool pushDownLeaf1=false, pushDownLeaf2=false;
				if(graph[ra1.cv2]->ant1==NULL && graph[ra1.cv3]->ant1!=NULL) pushDownLeaf1=true;
				if(graph[ra2.cv2]->ant1==NULL && graph[ra2.cv3]->ant1!=NULL) pushDownLeaf2=true;

				if(pushDownLeaf1 && !pushDownLeaf2) choose=1;
				else if(pushDownLeaf2 && !pushDownLeaf1) choose=2;
				//Break ties randomly
				else { if(rand()%2==0)choose=1; else choose=2; }*/
			}
		}
	}
	assert(choose!=-1);
	return choose;
}

// HEURISTICS TO GUIDE SIMPLIFICATION OF INTERPOLANT
//
// TABLE OF TRANSFORMATIONS
//(notice that A1 always produces an interpolant more complex but equivalent to the original one)
//
// I1	I2
//	  s		I3
//		 t
//
// |-----------------------------------------------------------------------------------------------------------------------------------------------------|
// | piv col | Original                                         | After A2,B2k                                     | After B1,B2              | After B3 |
// |-----------------------------------------------------------------------------------------------------------------------------------------------------|
// | A   A   | I1 or I2 or I3                                   | I1 or I3 or I2                                   | I1 or I3                 | I2       |
// | A   B   | (I1 or I2) and I3                                | (I1 and I3) or I2                                | I1 and I3                |          |
// | B   B   | I1 and I2 and I3                                 | I1 and I3 and I2                                 | I1 and I3                |          |
// | B   A   | (I1 and I2) or I3                                | (I1 or I3) and I2                                | I1 or I3                 |          |
// | A   AB  | (t or I1 or I2) and (~t or I3)                   | ((I1 or t) and (I3 or ~t)) or I2                 | (I1 or t) and (I3 or ~t) |          |
// | B   AB  | (t or (I1 and I2)) and (~t or I3)                | (I1 or t) and (I3 or ~t) and I2                  | (I1 or t) and (I3 or ~t) |          |
// | AB  A   | ((s or I1) and (~s or I2)) or I3                 | (I1 or I3 or s) and (I2 or ~s)                   | I1 or I3                 |          |
// | AB  B   | (s or I1) and (~s or I2) and I3                  | (s or (I1 and I3)) and (~s or I2)                | I1 and I3                |          |
// | AB  AB  | (((s or I1) and (~s or I2)) or t) and (I3 or ~t) | (((I1 or t) and (I3 or ~t)) or s) and (I2 or ~s) | (I1 or t) and (I3 or ~t) |          |
// |-----------------------------------------------------------------------------------------------------------------------------------------------------|


// Input: a context for a swap rule
// Output: true if rule application is allowed
// TODO it works now only for the middle interpolant masks
bool ProofGraph::allowRuleInterpolation( RuleContext & ra, bool duplAllowed )
{
  // FIXME: useless parameter
  (void)duplAllowed;
  //Determine number of partitions
  unsigned num_partitions = egraph.getNofPartitions();
  //Interpolant partition masks
  ipartitions_t A_mask = 0;
  ipartitions_t B_mask = 0;

  // Split approximately in half
  unsigned curr_interp_index = num_partitions/2;

  //Update current interpolant partition mask
  //Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
  if( curr_interp_index != 0 ) 
  {
    // A_mask = A_mask | SETBIT(curr_interp_index);
    setbit( A_mask, curr_interp_index );
  }
  //Determine mask corresponding to B
  B_mask = ~A_mask;
  //Reset bit 0 to 0
  // B_mask = B_mask & ~(SETBIT(0));
  clrbit( B_mask, 0 );

  // Retrieve partial interpolants
  ProofNode * v1 = graph[ra.cv1];
  ProofNode * v2 = graph[ra.cv2];
  ProofNode * v3 = graph[ra.cv3];
  assert( v1 );
  assert( v2 );
  assert( v3 );
  ProofNode * v  = graph[ra.cv];
  Var s = graph[ra.cw]->getPivot();
  Var t = graph[ra.cv]->getPivot();
  rul_type ty = ra.type;
  // FIXME: useless variable
  // bool dupl_nec =( graph[ra.cw]->res.size()>1);
  Enode * I1 = getPartialInterp( v1, curr_interp_index );
  assert( I1 );
  Enode * I2 = getPartialInterp( v2, curr_interp_index );
  assert( I2 );
  Enode * I3 = getPartialInterp( v3, curr_interp_index );
  assert( I3 );
  Enode * curr_interp = getPartialInterp( v, curr_interp_index );

  // Get pivot colors
  icolor_t s_color = getVarColor( s, A_mask, B_mask );
  icolor_t t_color = getVarColor( t, A_mask, B_mask );

  if(usingPudlakInterpolation())
  {
    // Calculate interpolant as it would be after rule application
    // rA1,rA2,rA2u,rB2k,rB3,rB1,rB2,rA1B,rA2B,rA1undo
    Enode * potential_interp=NULL;
    if( s_color == I_A && t_color == I_A )
    {
      if( ty == rA2 || ty == rB2k || ty == rA2u || ty == rA2B )
      {
	// equivalent interpolant
	return true;
      }
      else if ( ty == rB1 || ty == rB2)
      {
	potential_interp = egraph.mkOr( egraph.cons( I1
	                              , egraph.cons( I3 ) ) );
      }
      else if ( ty == rB3)
      {
	potential_interp = I2;
      }
      else return false;
    }
    else if ( s_color == I_A && t_color == I_B )
    {
      if( ty == rA2 || ty == rB2k || ty == rA2u || ty == rA2B )
      {
	potential_interp = egraph.mkOr( egraph.cons( egraph.mkAnd( egraph.cons( I1
		                                                 , egraph.cons( I3 ) ) )
	                              , egraph.cons( I2 ) ) );
      }
      else if ( ty == rB1 || ty == rB2 )
      {
	potential_interp = egraph.mkAnd( egraph.cons( I1
	                               , egraph.cons( I3 ) ) );
      }
      else if ( ty == rB3 )
      {
	potential_interp = I2;
      }
      else 
	return false;
    }
    else if ( s_color == I_B && t_color == I_B )
    {
      if( ty == rA2 || ty == rB2k || ty == rA2u || ty == rA2B )
      {
	// equivalent interpolant
	return true;
      }
      else if ( ty == rB1 || ty == rB2 )
      {
	potential_interp = egraph.mkAnd( egraph.cons( I1
	                               , egraph.cons( I3 ) ) );
      }
      else if ( ty == rB3 )
      {
	potential_interp = I2;
      }
      else 
	return false;
    }
    else if ( s_color == I_B && t_color == I_A )
    {
      if( ty == rA2 || ty == rB2k || ty == rA2u || ty == rA2B )
      {
	potential_interp = egraph.mkAnd( egraph.cons( egraph.mkOr( egraph.cons( I1
		                                                 , egraph.cons( I3 ) ) )
	                               , egraph.cons( I2 ) ) );
      }
      else if ( ty == rB1 || ty == rB2 )
      {
	potential_interp = egraph.mkOr( egraph.cons( I1
	                              , egraph.cons( I3 ) ) );
      }
      else if ( ty == rB3 )
      {
	potential_interp = I2;
      }
      else 
	return false;
    }
    else if ( s_color == I_A && t_color == I_AB )
    {
      if( ty == rA2 || ty == rB2k || ty == rA2u || ty == rA2B )
      {
	Enode * a = egraph.mkOr( egraph.cons( I1
	                       , egraph.cons( thandler->varToEnode( t ) ) ) );
	Enode * b = egraph.mkOr( egraph.cons( I3
	                       , egraph.cons( egraph.mkNot( egraph.cons( thandler->varToEnode( t ) ) ) ) ) );
	Enode * c = egraph.mkAnd( egraph.cons( a
	                        , egraph.cons( b ) ) );
	potential_interp = egraph.mkOr( egraph.cons( c
	                              , egraph.cons( I2 ) ) );
      }
      else if ( ty == rB1 || ty == rB2 )
      {
	Enode * a = egraph.mkOr( egraph.cons( I1
	                       , egraph.cons( thandler->varToEnode( t ) ) ) );
	Enode * b = egraph.mkOr( egraph.cons( I3
	                       , egraph.cons( egraph.mkNot( egraph.cons( thandler->varToEnode( t ) ) ) ) ) );
	potential_interp = egraph.mkAnd( egraph.cons( a
	                               , egraph.cons( b ) ) );
      }
      else if ( ty == rB3 )
      {
	potential_interp = I2;
      }
      else 
	return false;
    }
    else if ( s_color == I_B && t_color == I_AB )
    {
      if( ty == rA2 || ty == rB2k || ty == rA2u || ty == rA2B )
      {
	Enode * a = egraph.mkOr( egraph.cons( I1
	                       , egraph.cons( thandler->varToEnode( t ) ) ) );
	Enode * b = egraph.mkOr( egraph.cons( I3
	                       , egraph.cons( egraph.mkNot( egraph.cons( thandler->varToEnode( t ) ) ) ) ) );
	Enode * c = egraph.mkAnd( egraph.cons( a
	                        , egraph.cons( b ) ) );
	potential_interp = egraph.mkAnd( egraph.cons( c
	                               , egraph.cons( I2 ) ) );
      }
      else if ( ty == rB1 || ty == rB2 )
      {
	Enode * a = egraph.mkOr( egraph.cons( I1
	                       , egraph.cons( thandler->varToEnode( t ) ) ) );
	Enode * b = egraph.mkOr( egraph.cons( I3
	                       , egraph.cons( egraph.mkNot( egraph.cons( thandler->varToEnode( t ) ) ) ) ) );
	potential_interp = egraph.mkAnd( egraph.cons( a
	                               , egraph.cons( b ) ) );
      }
      else if ( ty == rB3 )
      {
	potential_interp = I2;
      }
      else return false;
    }
    else if ( s_color == I_AB && t_color == I_A )
    {
      if( ty == rA2 || ty == rB2k || ty == rA2u || ty == rA2B )
      {
	Enode * a = egraph.mkOr( egraph.cons( I1
	                       , egraph.cons( I3
			       , egraph.cons( thandler->varToEnode( s ) ) ) ) );
	Enode * b = egraph.mkOr( egraph.cons( I2
	                       , egraph.cons( egraph.mkNot( egraph.cons( thandler->varToEnode( s ) ) ) ) ) );
	potential_interp = egraph.mkAnd( egraph.cons( a
	                               , egraph.cons( b ) ) );
      }
      else if ( ty == rB1 || ty == rB2 )
      {
	potential_interp = egraph.mkOr( egraph.cons( I1
	                              , egraph.cons( I3 ) ) );
      }
      else if ( ty == rB3 )
      {
	potential_interp = I2;
      }
      else 
	return false;
    }
    else if ( s_color == I_AB && t_color == I_B )
    {
      if( ty == rA2 || ty == rB2k || ty == rA2u || ty == rA2B )
      {
	Enode * a = egraph.mkAnd( egraph.cons( I1
	                        , egraph.cons( I3 ) ) );
	Enode * b = egraph.mkOr( egraph.cons( a
	                       , egraph.cons( thandler->varToEnode( s ) ) ) );
	Enode * c = egraph.mkOr( egraph.cons( I2
	                       , egraph.cons( egraph.mkNot( egraph.cons( thandler->varToEnode( s ) ) ) ) ) );
	potential_interp = egraph.mkAnd( egraph.cons( b
	                               , egraph.cons( c ) ) );
      }
      else if ( ty == rB1 || ty == rB2 )
      {
	potential_interp = egraph.mkAnd( egraph.cons( I1
	                               , egraph.cons( I3 ) ) );
      }
      else if ( ty == rB3 )
      {
	potential_interp = I2;
      }
      else return false;
    }
    else if ( s_color == I_AB && t_color == I_AB )
    {
      if( ty == rA2 || ty == rB2k || ty == rA2u || ty == rA2B )
      {
	Enode * a = egraph.mkOr( egraph.cons( I1
	                       , egraph.cons( thandler->varToEnode( t ) ) ) );
	Enode * b = egraph.mkOr( egraph.cons( I3
	                       , egraph.cons( egraph.mkNot( egraph.cons( thandler->varToEnode( t ) ) ) ) ) );
	Enode * c = egraph.mkAnd( egraph.cons( a
	                        , egraph.cons( b ) ) );
	Enode * d = egraph.mkOr( egraph.cons( c
	                       , egraph.cons( thandler->varToEnode( s ) ) ) );
	Enode * e = egraph.mkOr( egraph.cons( I2
	                       , egraph.cons( egraph.mkNot( egraph.cons( thandler->varToEnode( s ) ) ) ) ) );
	potential_interp = egraph.mkAnd( egraph.cons( d
	                               , egraph.cons( e ) ) );
      }
      else if ( ty == rB1 || ty == rB2 )
      {
	Enode * a = egraph.mkOr( egraph.cons( I1
	                       , egraph.cons( thandler->varToEnode( t ) ) ) );
	Enode * b = egraph.mkOr( egraph.cons( I3
	                       , egraph.cons( egraph.mkNot( egraph.cons( thandler->varToEnode( t ) ) ) ) ) );
	potential_interp = egraph.mkAnd( egraph.cons( a
	                               , egraph.cons( b ) ) );
      }
      else if ( ty == rB3 )
      {
	potential_interp = I2;
      }
      else 
	return false;
    }
    else 
      opensmt_error( "this line should be unreachable" );

    // TODO improve criterion
    //if(dupl_nec && !(isCutRule(ty) || ty == rB2k)) return false;

    // TODO first strategy: allow rule if set of interpolant predicates stays the same or decreases
    int size1 = getPredicatesSetFromInterpolantIterative( curr_interp ).size( );
    int size2 = getPredicatesSetFromInterpolantIterative( potential_interp ).size( );
    if( size2 < size1 ) 
      return true;
    else if( size2 == size1 )
    {
      // TODO second strategy: allow rule if interpolant complexity stays the same or decreases
      int compl1 = getComplexityInterpolantIterative( curr_interp, false );
      int compl2 = getComplexityInterpolantIterative( potential_interp, false );
      if( compl2 <= compl1 ) 
	return true;
      else 
	return false;
    }
    else 
      return false;
  }
  opensmt_error( "this line should be unreachable" );
  return false;
}

#endif
