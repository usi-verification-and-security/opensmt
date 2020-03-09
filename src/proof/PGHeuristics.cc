/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

Periplo -- Copyright (C) 2013, Simone Fulvio Rollini

Periplo is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Periplo is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Periplo. If not, see <http://www.gnu.org/licenses/>.
 *********************************************************************/

#include "PG.h"


//Input: a context for a swap rule, a predicate to be pushed up
//Output: true if rule application is allowed
bool ProofGraph::allowSwapRuleForPredicatePushingUp(RuleContext& ra, Var pred)
{
	rul_type t=ra.getType();
	bool dupl=(getNode(ra.getW())->getNumResolvents()>1);

	Var pred1 = ( getNode(ra.getW())->getPivot() );
	Var pred2 = ( getNode(ra.getV())->getPivot() );
	bool is1 = ( pred1==pred );
	bool is2 = ( pred2==pred );

	if(is1 && is2)
	{
		if(!dupl)
		{
			// Both pred, swap only if a reduction is possible
			// and no duplication is needed
			if(t==rB2) return true;
			if(t==rA2B) return true;
			if(t==rA1prime) return true;
		}
	}
	else if(is1)
	{
		// Upper pred, do not allow

	}
	else if(is2)
	{
		// Lower pred, allow
		return true;
	}
	else
	{
		// Other predicates, do nothing
	}
	return false;
}

//Input: a context for a swap rule, a predicate to be pushed up
//Output: true if rule application is allowed
bool ProofGraph::allowSwapRuleForPredicatePushingDown(RuleContext& ra, Var pred)
{
	//cerr << "SWAP-Trying to push down " << thandler->varToEnode(pred) <<
	//	" where w=" << ra.getW() << " and v=" << ra.getV() << endl;

	Var pred1 = ( getNode(ra.getW())->getPivot() );
	Var pred2 = ( getNode(ra.getV())->getPivot() );
	bool is1 = (pred1==pred);
	bool is2 = (pred2==pred);

	if(is1 && is2) { opensmt_error_(); }
	else if(is1)
	{
		// Upper pred, allow
		//if( dupl ) return false;
		//if( t==rA1 || t==rA1B ) return false;
		return true;
	}
	else if(is2)
	{
		// Lower pred, do not allow
	}
	else
	{
		// Other predicates, do nothing
	}
	return false;
}

//Input: a context for a swap rule, a predicate to be pushed up
//Output: true if rule application is allowed
bool ProofGraph::allowCutRuleForPredicatePushing(RuleContext& ra, Var pred)
{
	bool dupl=(getNode(ra.getW())->getNumResolvents()>1);

	Var pred1 = ( getNode(ra.getW())->getPivot() );
	Var pred2 = ( getNode(ra.getV())->getPivot() );
	bool is1 = (pred1==pred);
	bool is2 = (pred2==pred);

	if(is1 && is2) { opensmt_error_(); }
	else if(is1) return true;
	else if(is2) return true;
	else
	{
		if(!dupl) return true;
	}
	return false;
}

//Input: a pair of left/right contexts
//Output: 0,1,2 to apply no rule, rule1, rule2
short ProofGraph::handleRuleApplicationForPredicatePushing(RuleContext& ra1,RuleContext& ra2, const ipartitions_t& mask)
{
	/*	cerr << "Examining (w=" << ra1.getW() << ",v="
			<< ra1.getV() << "," << ra1.getType() <<") and (w="
			<< ra2.getW() << ",v=" << ra2.getV() << "," << ra2.getType() << ")" << endl;*/

	//TODO generalize
	Var pred = pred_to_push;
	bool push_up = false;

	// Swap application rule
	bool(ProofGraph::*allowSwap)(RuleContext& ra,Var v) = &ProofGraph::allowSwapRuleForPredicatePushingDown;
	// Cut application rule
	bool(ProofGraph::*allowCut)(RuleContext& ra,Var v) = &ProofGraph::allowCutRuleForPredicatePushing;

	// Check need for duplication
	bool dupl1, dupl2;
	bool allowed1, allowed2;

	short chosen=-1;
	rul_type t1=ra1.getType();
	rul_type t2=ra2.getType();
	bool is1cut=isCutRule(t1);
	bool is2cut=isCutRule(t2);
	bool is1swap=isSwapRule(t1);
	bool is2swap=isSwapRule(t2);

	//rA1,rA2,rA2u,rA1B,rA2B,rA1undo,rB2k,rB3,rB1,rB2

	//Neither applicable
	if(ra1.disabled() && ra2.disabled())
		chosen=0;
	//First not applicable
	else if(ra1.disabled() && ra2.enabled())
	{
		if( is2cut ) allowed2 =  (*this.*allowCut)(ra2,pred);
		else if( is2swap ) allowed2 = (*this.*allowSwap)(ra2,pred);
		else opensmt_error_();
		if(allowed2) chosen=2; else chosen=0;
	}
	//Second not applicable
	else if(ra1.enabled() && ra2.disabled())
	{
		if( is1cut ) allowed1 =  (*this.*allowCut)(ra1,pred);
		else if( is1swap ) allowed1 = (*this.*allowSwap)(ra1,pred);
		else opensmt_error_();
		if(allowed1) chosen=1; else chosen=0;
	}
	//Both applicable
	else if(ra1.enabled() && ra2.enabled())
	{
		if( is1cut ) allowed1 =  (*this.*allowCut)(ra1,pred);
		else if( is1swap ) allowed1 = (*this.*allowSwap)(ra1,pred);
		else opensmt_error_();

		if( is2cut ) allowed2 =  (*this.*allowCut)(ra2,pred);
		else if( is2swap ) allowed2 = (*this.*allowSwap)(ra2,pred);
		else opensmt_error_();

		//Neither allowed
		if(!allowed1 && !allowed2) chosen=0;
		//First allowed
		else if(allowed1 && !allowed2) chosen=1;
		//Second allowed
		else if(!allowed1 && allowed2) chosen=2;
		//Both allowed
		else if(allowed1 && allowed2)
		{
			//Case one cuts, the other swaps: privilege cut
			if(is1cut && is2swap) chosen=1;
			else if(is2cut && is1swap) chosen=2;
			//Case both cut
			else if(is1cut && is2cut)
			{
				//NOTE Privilege the one with the relevant predicate?
				//NOTE probably not necessary
				//Privilege B3 over B1 and B2
				if(t1==rB3 && t2!=rB3) chosen=1;
				else if(t1!=rB3 && t2==rB3) chosen=2;
				//Break ties randomly
				else { if(rand()%2==0) chosen=1; else chosen=2; }
			}
			//Case both swap
			else if(is2swap && is1swap)
			{
				//NOTE Privilege the one with the relevant predicate!
				// v pivot is to be pushed up
				Var	x1, x2;
				if( push_up )
				{
					x1 = getNode(ra1.getV())->getPivot();
					x2 = getNode(ra2.getV())->getPivot();
				}
				// w pivot is to be pushed down
				else
				{
					x1 = getNode(ra1.getW())->getPivot();
					x2 = getNode(ra2.getW())->getPivot();
				}
				if( x1 == pred && x2 != pred ) chosen = 1;
				else if( x1 != pred && x2 == pred ) chosen = 2;
				else
				{
					dupl1=(getNode(ra1.getW())->getNumResolvents() > 1);
					dupl2=(getNode(ra2.getW())->getNumResolvents() > 1);
					//Privilege the one not duplicating
					if(dupl1 && !dupl2) chosen=2;
					else if(!dupl1 && dupl2) chosen=1;
					//Privilege A1undo, then B2k, then A2 over A1
					else if(t1==rA1prime && t2!=rA1prime) chosen=1;
					else if(t1!=rA1prime && t2==rA1prime) chosen=2;
					else if(t1==rB2 && t2!=rB2) chosen=1;
					else if(t1!=rB2 && t2==rB2) chosen=2;
					else if((t1==rA2 || t1==rA2u || t1==rA2B) && (t2==rA1 || t2==rA1B)) chosen=1;
					else if((t2==rA2 || t2==rA2u || t2==rA2B) && (t1==rA1 || t1==rA1B)) chosen=2;
					//Privilege A2B over A2 and A1B over A1
					else if((t1==rA2B && (t2==rA2 || t2==rA2u)) || (t1==rA1B && t2==rA1)) chosen=1;
					else if((t2==rA2B && (t1==rA2 || t1==rA2u)) || (t2==rA1B && t1==rA1)) chosen=2;
					//Break ties randomly
					else{ if(rand()%2==0) chosen=1; else chosen=2; }
				}
			}
		}
	}
	assert(chosen!=-1);
	return chosen;
}

//Input: a context for a swap rule
//Output: true if rule application is allowed
bool ProofGraph::allowSwapRuleForUnitsPushingDown(RuleContext& ra)
{
	rul_type t=ra.getType();
	bool dupl=(getNode(ra.getW())->getNumResolvents()>1);
	if(dupl) return false;

	bool unit1 = ( getNode(ra.getV2())->getClauseSize() == 1 );
	bool unit2 = ( getNode(ra.getV3())->getClauseSize() == 1 );

	if(unit1 && unit2)
	{
		assert(t!=rA1 && t!=rA1B);
		// Both units, swap only if a reduction is possible
		if(t==rB2) return true;
		if(t==rA2B) return true;
		if(t==rA1prime) return true;
	}
	else if(unit1)
	{
		assert(t!=rA1 && t!=rA1B);
		// Upper unit, allow
		return true;
	}
	else if(unit2)
	{
		// Lower unit, do not allow
	}
	else
	{
		// No units, do not allow
	}
	return false;
}


//Input: a pair of left/right contexts
//Output: 0,1,2 to apply no rule, rule1, rule2
short ProofGraph::handleRuleApplicationForUnitsPushingDown(RuleContext& ra1,RuleContext& ra2, const ipartitions_t& mask)
{
	// Swap application rule
	bool(ProofGraph::*allowSwap)(RuleContext& ra) = &ProofGraph::allowSwapRuleForUnitsPushingDown;

	// Check need for duplication
	bool dupl1, dupl2;
	bool allowed1, allowed2;

	short chosen=-1;
	rul_type t1=ra1.getType();
	rul_type t2=ra2.getType();
	bool is1cut=isCutRule(t1);
	bool is2cut=isCutRule(t2);
	bool is1swap=isSwapRule(t1);
	bool is2swap=isSwapRule(t2);

	//rA1,rA2,rA2u,rA1B,rA2B,rA1undo,rB2k,rB3,rB1,rB2

	//Neither applicable
	if(ra1.disabled() && ra2.disabled())
		chosen=0;
	//First not applicable
	else if(ra1.disabled() && ra2.enabled())
	{
		if( is2cut ) allowed2 = true;
		else if( is2swap ) allowed2 = (*this.*allowSwap)(ra2);
		else opensmt_error_();
		if(allowed2) chosen=2; else chosen=0;
	}
	//Second not applicable
	else if(ra1.enabled() && ra2.disabled())
	{
		if( is1cut ) allowed1 = true;
		else if( is1swap ) allowed1 = (*this.*allowSwap)(ra1);
		else opensmt_error_();
		if(allowed1) chosen=1; else chosen=0;
	}
	//Both applicable
	else if(ra1.enabled() && ra2.enabled())
	{
		if( is1cut ) allowed1 = true;
		else if( is1swap ) allowed1 = (*this.*allowSwap)(ra1);
		else opensmt_error_();

		if( is2cut ) allowed2 = true;
		else if( is2swap ) allowed2 = (*this.*allowSwap)(ra2);
		else opensmt_error_();

		//Neither allowed
		if(!allowed1 && !allowed2) chosen=0;
		//First allowed
		else if(allowed1 && !allowed2) chosen=1;
		//Second allowed
		else if(!allowed1 && allowed2) chosen=2;
		//Both allowed
		else if(allowed1 && allowed2)
		{
			//Case one cuts, the other swaps: privilege cut
			if(is1cut && is2swap) chosen=1;
			else if(is2cut && is1swap) chosen=2;
			//Case both cut
			else if(is1cut && is2cut)
			{
				//Privilege B3 over B1 and B2
				if(t1==rB3 && t2!=rB3) chosen=1;
				else if(t1!=rB3 && t2==rB3) chosen=2;
				//Break ties randomly
				else { if(rand()%2==0)chosen=1; else chosen=2; }
			}
			//Case both swap
			else if(is2swap && is1swap)
			{
				dupl1=(getNode(ra1.getW())->getNumResolvents() > 1);
				dupl2=(getNode(ra2.getW())->getNumResolvents() > 1);
				//Privilege the one not duplicating
				if(dupl1 && !dupl2) chosen=2;
				else if(!dupl1 && dupl2) chosen=1;
				//Privilege A1undo, then B2k, then A2 over A1
				else if(t1==rA1prime && t2!=rA1prime) chosen=1;
				else if(t1!=rA1prime && t2==rA1prime) chosen=2;
				else if(t1==rB2 && t2!=rB2) chosen=1;
				else if(t1!=rB2 && t2==rB2) chosen=2;
				else if((t1==rA2 || t1==rA2u || t1==rA2B) && (t2==rA1 || t2==rA1B)) chosen=1;
				else if((t2==rA2 || t2==rA2u || t2==rA2B) && (t1==rA1 || t1==rA1B)) chosen=2;
				//Privilege A2B over A2 and A1B over A1
				else if((t1==rA2B && (t2==rA2 || t2==rA2u)) || (t1==rA1B && t2==rA1)) chosen=1;
				else if((t2==rA2B && (t1==rA2 || t1==rA2u)) || (t2==rA1B && t1==rA1)) chosen=2;
				//Break ties randomly
				else{ if(rand()%2==0) chosen=1; else chosen=2; }
			}
		}
	}
	assert(chosen!=-1);
	return chosen;
}

//Input: a context for a swap rule
//Output: true if rule application is allowed
bool ProofGraph::allowSwapRuleForReduction(RuleContext& ra)
{
	rul_type t=ra.getType();
	bool dupl=(getNode(ra.getW())->getNumResolvents()>1);

	if(!dupl)
	{
		// Push up if it has more resolvents
		unsigned long sp2 = getNode(ra.getV2())->getNumResolvents();
		unsigned long sp3 = getNode(ra.getV3())->getNumResolvents();
		if(sp2 <= sp3)
		{
			//Always allow rB2k
			if(t==rB2) return true;
			//Allow A1 undo if no duplications
			if(t==rA1prime) return true;
			//Allow A2 if no duplications
			if(t==rA2B) return true;
			if(t==rA2 || t==rA2u) return true;
			//if(t==rA1B && !dupl) return true;
		}
	}
	//Don't allow the rest
	return false;
}

//Input: a context for a cut rule
//Output: true if rule application is allowed
bool ProofGraph::allowCutRuleForReduction(RuleContext& ra)
{
	rul_type t=ra.getType();

	if( t==rB1 ) return true;
	else if( t==rB2prime ) return true;
	else if( t==rB3 ) return true;
	else opensmt_error_();
}

//Input: a pair of left/right contexts
//Output: 0,1,2 to apply no rule, rule1, rule2
short ProofGraph::handleRuleApplicationForReduction(RuleContext& ra1,RuleContext& ra2, const ipartitions_t& mask)
{
	// Randomize application of rules
	if( additionalRandomization() && rand()%2==0 ) return 0;

	// Swap application rule
	bool(ProofGraph::*allowSwap)(RuleContext& ra) = &ProofGraph::allowSwapRuleForReduction;
	// Swap application rule
	bool(ProofGraph::*allowCut)(RuleContext& ra) = &ProofGraph::allowCutRuleForReduction;

	// Check need for duplication
	bool dupl1, dupl2;
	bool allowed1, allowed2;

	short chosen=-1;
	rul_type t1=ra1.getType();
	rul_type t2=ra2.getType();
	bool is1cut=isCutRule(t1);
	bool is2cut=isCutRule(t2);
	bool is1swap=isSwapRule(t1);
	bool is2swap=isSwapRule(t2);

	//rA1,rA2,rA2u,rA1B,rA2B,rA1undo,rB2k,rB3,rB1,rB2

	//Neither applicable
	if(ra1.disabled() && ra2.disabled())
		chosen=0;
	//First not applicable
	else if(ra1.disabled() && ra2.enabled())
	{
		if( is2cut ) allowed2 =  (*this.*allowCut)(ra2);
		else if( is2swap ) allowed2 = (*this.*allowSwap)(ra2);
		else opensmt_error_();
		if(allowed2) chosen=2; else chosen=0;
	}
	//Second not applicable
	else if(ra1.enabled() && ra2.disabled())
	{
		if( is1cut ) allowed1 =  (*this.*allowCut)(ra1);
		else if( is1swap ) allowed1 = (*this.*allowSwap)(ra1);
		else opensmt_error_();
		if(allowed1) chosen=1; else chosen=0;
	}
	//Both applicable
	else if(ra1.enabled() && ra2.enabled())
	{
		if( is1cut ) allowed1 =  (*this.*allowCut)(ra1);
		else if( is1swap ) allowed1 = (*this.*allowSwap)(ra1);
		else opensmt_error_();

		if( is2cut ) allowed2 =  (*this.*allowCut)(ra2);
		else if( is2swap ) allowed2 = (*this.*allowSwap)(ra2);
		else opensmt_error_();

		//Neither allowed
		if(!allowed1 && !allowed2) chosen=0;
		//First allowed
		else if(allowed1 && !allowed2) chosen=1;
		//Second allowed
		else if(!allowed1 && allowed2) chosen=2;
		//Both allowed
		else if(allowed1 && allowed2)
		{
			//Case one cuts, the other swaps: privilege cut
			if(is1cut && is2swap) chosen=1;
			else if(is2cut && is1swap) chosen=2;
			//Case both cut
			else if(is1cut && is2cut)
			{
				//Privilege B3 over B1 and B2
				if(t1==rB3 && t2!=rB3) chosen=1;
				else if(t1!=rB3 && t2==rB3) chosen=2;
				//Break ties randomly
				else
				{
					if(rand()%2==0)chosen=1; else chosen=2;
				}
			}
			//Case both swap
			else if(is2swap && is1swap)
			{
				dupl1=(getNode(ra1.getW())->getNumResolvents() > 1);
				dupl2=(getNode(ra2.getW())->getNumResolvents() > 1);
				//Privilege the one not duplicating
				if(dupl1 && !dupl2) chosen=2;
				else if(!dupl1 && dupl2) chosen=1;
				//Privilege A1undo, then B2k, then A2 over A1
				else if(t1==rA1prime && t2!=rA1prime) chosen=1;
				else if(t1!=rA1prime && t2==rA1prime) chosen=2;
				else if(t1==rB2 && t2!=rB2) chosen=1;
				else if(t1!=rB2 && t2==rB2) chosen=2;
				else if((t1==rA2 || t1==rA2u || t1==rA2B) && (t2==rA1 || t2==rA1B)) chosen=1;
				else if((t2==rA2 || t2==rA2u || t2==rA2B) && (t1==rA1 || t1==rA1B)) chosen=2;
				//Privilege A2B over A2 and A1B over A1
				else if((t1==rA2B && (t2==rA2 || t2==rA2u)) || (t1==rA1B && t2==rA1)) chosen=1;
				else if((t2==rA2B && (t1==rA2 || t1==rA2u)) || (t2==rA1B && t1==rA1)) chosen=2;
				//Break ties randomly
				else
				{
					swap_ties++;
					if(rand()%2==0) chosen=1; else chosen=2;
				}
			}
		}
	}
	assert(chosen!=-1);
	return chosen;
}

//Input: a context for a swap rule
//Output: true if rule application is allowed
bool ProofGraph::allowSwapRuleForStrongerWeakerInterpolant(RuleContext& ra, const ipartitions_t& mask)
{
	rul_type t=ra.getType();
	bool dupl=(getNode(ra.getW())->getNumResolvents()>1);
	// Light technique: no duplications allowed
	if(dupl) return false;
	// No creation of new nodes or simplifications allowed
	if(t==rA1 || t==rA1B || t==rB2 || t==rA1prime) return false;
	assert(t==rA2 || t==rA2B || t==rA2u);

	// McMillan/McMillan'/Pudlak should be used
	assert( usingMcMillanInterpolation() || usingPudlakInterpolation() || usingMcMillanPrimeInterpolation() );
	// Check colors of the two pivots
	icolor_t piv_w_color = getVarClass2( getNode(ra.getW())->getPivot() );
	if(  piv_w_color == I_AB )
	{
		if( usingMcMillanInterpolation() ) piv_w_color = I_B;
		if( usingMcMillanPrimeInterpolation() ) piv_w_color = I_A;
	}
	icolor_t piv_v_color = getVarClass2( getNode(ra.getV())->getPivot() );

	if(  piv_v_color == I_AB )
	{
		if( usingMcMillanInterpolation() ) piv_v_color = I_B;
		if( usingMcMillanPrimeInterpolation() ) piv_v_color = I_A;
	}

	if( restructuringForStrongerInterpolant() )
	{
	// The new interpolant is stronger than the original one for the following
	// pairs of pivot colors: (b,a) (ab,a) (b,ab)
	if(		(piv_w_color == I_B && piv_v_color == I_A) ||
			(piv_w_color == I_AB && piv_v_color == I_A ) ||
			(piv_w_color == I_B && piv_v_color == I_AB))
		return true;
	else
		return false;
	}
	else if( restructuringForWeakerInterpolant() )
	{
		// The new interpolant is stronger than the original one for the following
		// pairs of pivot colors: (a,b) (a,ab) (ab,b)
		if(		(piv_w_color == I_A && piv_v_color == I_B) ||
				(piv_w_color == I_A && piv_v_color == I_AB ) ||
				(piv_w_color == I_AB && piv_v_color == I_B))
			return true;
		else
			return false;
	}
	else opensmt_error_();
}


//Input: a pair of left/right contexts
//Output: 0,1,2 to apply no rule, rule1, rule2
short ProofGraph::handleRuleApplicationForStrongerWeakerInterpolant(RuleContext& ra1,RuleContext& ra2, const ipartitions_t& mask)
{
	// Swap application rule
	bool(ProofGraph::*allowSwap)(RuleContext&, const ipartitions_t&) = &ProofGraph::allowSwapRuleForStrongerWeakerInterpolant;

	// Check need for duplication
	bool dupl1, dupl2;
	bool allowed1, allowed2;

	short chosen=-1;
	rul_type t1=ra1.getType();
	rul_type t2=ra2.getType();
	bool is1cut=isCutRule(t1);
	bool is2cut=isCutRule(t2);
	bool is1swap=isSwapRule(t1);
	bool is2swap=isSwapRule(t2);

	//rA1,rA2,rA2u,rA1B,rA2B,rA1undo,rB2k,rB3,rB1,rB2

	//Neither applicable
	if(ra1.disabled() && ra2.disabled())
		chosen=0;
	//First not applicable
	else if(ra1.disabled() && ra2.enabled())
	{
		if( is2cut ) allowed2 =  false;
		else if( is2swap ) allowed2 = (*this.*allowSwap)(ra2, mask);
		else opensmt_error_();
		if(allowed2) chosen=2; else chosen=0;
	}
	//Second not applicable
	else if(ra1.enabled() && ra2.disabled())
	{
		if( is1cut ) allowed1 =  false;
		else if( is1swap ) allowed1 = (*this.*allowSwap)(ra1, mask);
		else opensmt_error_();
		if(allowed1) chosen=1; else chosen=0;
	}
	//Both applicable
	else if(ra1.enabled() && ra2.enabled())
	{
		if( is1cut ) allowed1 = false;
		else if( is1swap ) allowed1 = (*this.*allowSwap)(ra1, mask);
		else opensmt_error_();

		if( is2cut ) allowed2 =  false;
		else if( is2swap ) allowed2 = (*this.*allowSwap)(ra2, mask);
		else opensmt_error_();

		//Neither allowed
		if(!allowed1 && !allowed2) chosen=0;
		//First allowed
		else if(allowed1 && !allowed2) chosen=1;
		//Second allowed
		else if(!allowed1 && allowed2) chosen=2;
		//Both allowed
		else if(allowed1 && allowed2)
		{
			//Case one cuts, the other swaps: privilege cut
			if(is1cut && is2swap) chosen=1;
			else if(is2cut && is1swap) chosen=2;
			//Case both cut
			else if(is1cut && is2cut)
			{
				//Privilege B3 over B1 and B2
				if(t1==rB3 && t2!=rB3) chosen=1;
				else if(t1!=rB3 && t2==rB3) chosen=2;
				//Break ties randomly
				else
				{
					if(rand()%2==0)chosen=1; else chosen=2;
				}
			}
			//Case both swap
			else if(is2swap && is1swap)
			{
				dupl1=(getNode(ra1.getW())->getNumResolvents() > 1);
				dupl2=(getNode(ra2.getW())->getNumResolvents() > 1);
				//Privilege the one not duplicating
				if(dupl1 && !dupl2) chosen=2;
				else if(!dupl1 && dupl2) chosen=1;
				//Privilege A1undo, then B2k, then A2 over A1
				else if(t1==rA1prime && t2!=rA1prime) chosen=1;
				else if(t1!=rA1prime && t2==rA1prime) chosen=2;
				else if(t1==rB2 && t2!=rB2) chosen=1;
				else if(t1!=rB2 && t2==rB2) chosen=2;
				else if((t1==rA2 || t1==rA2u || t1==rA2B) && (t2==rA1 || t2==rA1B)) chosen=1;
				else if((t2==rA2 || t2==rA2u || t2==rA2B) && (t1==rA1 || t1==rA1B)) chosen=2;
				//Privilege A2B over A2 and A1B over A1
				else if((t1==rA2B && (t2==rA2 || t2==rA2u)) || (t1==rA1B && t2==rA1)) chosen=1;
				else if((t2==rA2B && (t1==rA2 || t1==rA2u)) || (t2==rA1B && t1==rA1)) chosen=2;
				//Break ties randomly
				else
				{
					swap_ties++;
					if(rand()%2==0) chosen=1; else chosen=2;
				}
			}
		}
	}
	assert(chosen!=-1);
	return chosen;
}

//Input: a context for a swap rule
//Output: true if rule application is allowed
bool ProofGraph::allowSwapRuleForCNFinterpolant(RuleContext& ra)
{
	bool dupl=(getNode(ra.getW())->getNumResolvents()>1);

	// McMillan should be used for generating an interpolant in CNF
	assert( usingMcMillanInterpolation() );
	// Check colors of the two pivots
	// NOTE with McMillan algorithm the color of a pivot is always A or B
	icolor_t piv_w_color = getVarClass2( getNode(ra.getW())->getPivot() );
	if(  piv_w_color == I_AB ) piv_w_color = I_B;
	icolor_t piv_v_color = getVarClass2( getNode(ra.getV())->getPivot() );
	if(  piv_v_color == I_AB ) piv_v_color = I_B;
	assert(piv_w_color != I_AB && piv_v_color != I_AB);

	// NOTE A-colored pivots must stay above B-colored pivots
	if((piv_w_color == I_A && piv_v_color == I_A) || (piv_w_color == I_B && piv_v_color == I_B ))
	{
		return false;
	}
	else if (piv_w_color == I_B && piv_v_color == I_A)
	{
		if(dupl) return false;
		else return true;
	}
	else if (piv_w_color == I_A && piv_v_color == I_B)
	{
		return false;
	}
	else opensmt_error_();
}

//Input: a pair of left/right contexts
//Output: 0,1,2 to apply no rule, rule1, rule2
short ProofGraph::handleRuleApplicationForCNFinterpolant(RuleContext& ra1,RuleContext& ra2, const ipartitions_t& mask)
{
	// Swap application rule
	bool(ProofGraph::*allowSwap)(RuleContext& ra) = &ProofGraph::allowSwapRuleForCNFinterpolant;
	// Cut application rule
	bool(ProofGraph::*allowCut)(RuleContext& ra) = &ProofGraph::allowCutRuleForReduction;

	// Check need for duplication
	bool dupl1, dupl2;
	bool allowed1, allowed2;

	short chosen=-1;
	rul_type t1=ra1.getType();
	rul_type t2=ra2.getType();
	bool is1cut=isCutRule(t1);
	bool is2cut=isCutRule(t2);
	bool is1swap=isSwapRule(t1);
	bool is2swap=isSwapRule(t2);

	//rA1,rA2,rA2u,rA1B,rA2B,rA1undo,rB2k,rB3,rB1,rB2

	//Neither applicable
	if(ra1.disabled() && ra2.disabled())
		chosen=0;
	//First not applicable
	else if(ra1.disabled() && ra2.enabled())
	{
		if( is2cut ) allowed2 =  (*this.*allowCut)(ra2);
		else if( is2swap ) allowed2 = (*this.*allowSwap)(ra2);
		else opensmt_error_();
		if(allowed2) chosen=2; else chosen=0;
	}
	//Second not applicable
	else if(ra1.enabled() && ra2.disabled())
	{
		if( is1cut ) allowed1 =  (*this.*allowCut)(ra1);
		else if( is1swap ) allowed1 = (*this.*allowSwap)(ra1);
		else opensmt_error_();
		if(allowed1) chosen=1; else chosen=0;
	}
	//Both applicable
	else if(ra1.enabled() && ra2.enabled())
	{
		if( is1cut ) allowed1 =  (*this.*allowCut)(ra1);
		else if( is1swap ) allowed1 = (*this.*allowSwap)(ra1);
		else opensmt_error_();

		if( is2cut ) allowed2 =  (*this.*allowCut)(ra2);
		else if( is2swap ) allowed2 = (*this.*allowSwap)(ra2);
		else opensmt_error_();

		//Neither allowed
		if(!allowed1 && !allowed2) chosen=0;
		//First allowed
		else if(allowed1 && !allowed2) chosen=1;
		//Second allowed
		else if(!allowed1 && allowed2) chosen=2;
		//Both allowed
		else if(allowed1 && allowed2)
		{
			//Case one cuts, the other swaps: privilege cut
			if(is1cut && is2swap) chosen=1;
			else if(is2cut && is1swap) chosen=2;
			//Case both cut
			else if(is1cut && is2cut)
			{
				//Privilege B3 over B1 and B2
				if(t1==rB3 && t2!=rB3) chosen=1;
				else if(t1!=rB3 && t2==rB3) chosen=2;
				//Break ties randomly
				else
				{
					if(rand()%2==0)chosen=1; else chosen=2;
				}
			}
			//Case both swap
			else if(is2swap && is1swap)
			{
				dupl1=(getNode(ra1.getW())->getNumResolvents() > 1);
				dupl2=(getNode(ra2.getW())->getNumResolvents() > 1);
				//Privilege the one not duplicating
				if(dupl1 && !dupl2) chosen=2;
				else if(!dupl1 && dupl2) chosen=1;
				//Privilege A1undo, then B2k, then A2 over A1
				else if(t1==rA1prime && t2!=rA1prime) chosen=1;
				else if(t1!=rA1prime && t2==rA1prime) chosen=2;
				else if(t1==rB2 && t2!=rB2) chosen=1;
				else if(t1!=rB2 && t2==rB2) chosen=2;
				else if((t1==rA2 || t1==rA2u || t1==rA2B) && (t2==rA1 || t2==rA1B)) chosen=1;
				else if((t2==rA2 || t2==rA2u || t2==rA2B) && (t1==rA1 || t1==rA1B)) chosen=2;
				//Privilege A2B over A2 and A1B over A1
				else if((t1==rA2B && (t2==rA2 || t2==rA2u)) || (t1==rA1B && t2==rA1)) chosen=1;
				else if((t2==rA2B && (t1==rA2 || t1==rA2u)) || (t2==rA1B && t1==rA1)) chosen=2;
				//Break ties randomly
				else
				{
					swap_ties++;
					if(rand()%2==0) chosen=1; else chosen=2;
				}
			}
		}
	}
	assert(chosen!=-1);
	return chosen;
}


//Input: node to be replaced by either antecedent during restructuring
//Output: true if ant1 is chosen, false if ant2 is chosen
bool ProofGraph::chooseReplacingAntecedent( ProofNode* n )
{
	//1) If an antecedent has only one resolvent, choose the other
	//2) If both (or none) have only one resolvent, choose the smaller clause
	//3) Break ties randomly
	bool choose_ant1;
	assert(n->getAnt1()!=NULL && n->getAnt2()!=NULL);
	if(n->getAnt1()->getNumResolvents()==1 && n->getAnt2()->getNumResolvents()>1)
		choose_ant1=false;
	else if(n->getAnt1()->getNumResolvents()>1 && n->getAnt2()->getNumResolvents()==1)
		choose_ant1=true;
	else
	{
		if(n->getAnt1()->getClauseSize()> n->getAnt2()->getClauseSize()) choose_ant1=false;
		else if(n->getAnt2()->getClauseSize()> n->getAnt1()->getClauseSize()) choose_ant1=true;
		else
		{
			if(rand()%2==0)choose_ant1=true; else choose_ant1=false;
		}
	}
	return choose_ant1;
}

// HEURISTICS TO GUIDE SIMPLIFICATION OF INTERPOLANTS
//
// TABLE OF TRANSFORMATIONS
//(notice that A1 always produces an interpolant more complex but equivalent to the original one)
//
// I1	I2
//	  s		I3
//		 t
//
// |----------------------------------------------------------------------------------------------------------------------------------------------------------|
// | piv col | Original                                         |    | After A2,B2k                                     | After B1,B2              | After B3 |
// |----------------------------------------------------------------------------------------------------------------------------------------------------------|
// | A   A   | I1 or I2 or I3                                   | =  | I1 or I3 or I2                                   | I1 or I3                 | I2       |
// | A   B   | (I1 or I2) and I3                                | => | (I1 and I3) or I2                                | I1 and I3                |          |
// | B   B   | I1 and I2 and I3                                 | =  | I1 and I3 and I2                                 | I1 and I3                |          |
// | B   A   | (I1 and I2) or I3                                | <= | (I1 or I3) and I2                                | I1 or I3                 |          |
// | A   AB  | (t or I1 or I2) and (~t or I3)                   | => | ((I1 or t) and (I3 or ~t)) or I2                 | (I1 or t) and (I3 or ~t) |          |
// | B   AB  | (t or (I1 and I2)) and (~t or I3)                | <= | (I1 or t) and (I3 or ~t) and I2                  | (I1 or t) and (I3 or ~t) |          |
// | AB  A   | ((s or I1) and (~s or I2)) or I3                 | <= | (I1 or I3 or s) and (I2 or ~s)                   | I1 or I3                 |          |
// | AB  B   | (s or I1) and (~s or I2) and I3                  | => | (s or (I1 and I3)) and (~s or I2)                | I1 and I3                |          |
// | AB  AB  | (((s or I1) and (~s or I2)) or t) and (I3 or ~t) | ?  | (((I1 or t) and (I3 or ~t)) or s) and (I2 or ~s) | (I1 or t) and (I3 or ~t) |          |
// |----------------------------------------------------------------------------------------------------------------------------------------------------------|

// SIMPLIFICATIONS TABLE WHEN HAVING true and false
// |---------------------------------------------------------------------------------------------------------------------
// | piv col | Original                                         |    | After A2,B2k                                     |
// |---------------------------------------------------------------------------------------------------------------------
// | A   B   | (I1 or I2) and I3                                | => | (I1 and I3) or I2                                |
// | B   A   | (I1 and I2) or I3                                | <= | (I1 or I3) and I2                                |
// | A   AB  | (t or I1 or I2) and (~t or I3)                   | => | ((I1 or t) and (I3 or ~t)) or I2                 |
// | B   AB  | (t or (I1 and I2)) and (~t or I3)                | <= | (I1 or t) and (I3 or ~t) and I2                  |
// | AB  A   | ((s or I1) and (~s or I2)) or I3                 | <= | (I1 or I3 or s) and (I2 or ~s)                   |
// | AB  B   | (s or I1) and (~s or I2) and I3                  | => | (s or (I1 and I3)) and (~s or I2)                |
// | AB  AB  | (((s or I1) and (~s or I2)) or t) and (I3 or ~t) | ?  | (((I1 or t) and (I3 or ~t)) or s) and (I2 or ~s) |
// |---------------------------------------------------------------------------------------------------------------------
//
//   A   B     if I2=true            I3 -> true
//   B   A     if I2=false           I3 -> false
//   A   AB    if I2=true			 (~t or I3) -> true
//   B   AB    if I2=false           t and (~t or I3) -> false
//   AB  A     if I1=true            (~s or I2) or I3 -> (I2 or ~s)
//   AB  B     ?
//   AB  AB    ?
