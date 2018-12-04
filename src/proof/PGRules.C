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

#ifdef PRODUCE_PROOF
#include "PG.h"


// Check if a rule can be applied and if so, determine its context
// v3 and v are given in input
// ra is modified to contain the 5 nodes context
// Return false if w has not antecedents (that is, v1 and v2 don't exist)
bool ProofGraph::getRuleContext(clauseid_t idv3, clauseid_t idv, RuleContext& ra)
{
	ra.reset();
	ProofNode* v3=getNode(idv3);
	ProofNode* v=getNode(idv);

	assert((size_t)idv3<getGraphSize());
	assert(v3!=NULL);
	assert((size_t)idv<getGraphSize());
	assert(v!=NULL);

	assert(v->getAnt1()==v3 || v->getAnt2()==v3);
	// assert(v->getAnt1()->getId()==idv3 || v->getAnt2()->getId()==idv3);

	// Determine w, i.e. second antecedent v
	ProofNode* w=(v3==v->getAnt1()) ? v->getAnt2() : v->getAnt1();
	// If w has no antecedents, no rule can be applied
	if(w->isLeaf()) return false;

	// Resolution pivots
	Var t0=w->getPivot();
	Var t1=v->getPivot();

	// w antecedents are v1,v2; clauses are (t0 t1 C1) and (~t0 C2)
	// w clause is (t1 C1 C2)
	// v antecedents are w and v3; clauses are w clause and (~t1, C3)
	// v clause is (C1 C2 C3)

	bool found1, found2;
	size_t size;

	// Determine sign of t1 and t0 (if present) in v3
	bool t0_in_C3=false;
	bool sign_t0_C3=false; Lit l;

	short r0 = v3->hasOccurrenceBin(t0);
	if(r0 != -1) { t0_in_C3 = true; sign_t0_C3 = (r0 == 0)? false : true; }

	// Check condition: t1 not in C2
	bool t1_in_ant1=false, t1_in_ant2 =false;
	bool sign_t0_ant1=false, sign_t0_ant2=false;
	bool sign_t1_ant1=false, sign_t1_ant2=false;

	// Sign of t0
	short r1 = w->getAnt1()->hasOccurrenceBin(t0);
	assert(r1 != -1);
	if(r1 != -1) { sign_t0_ant1 = (r1 == 0)? false : true; }
	// Look for t1
	r1 = w->getAnt1()->hasOccurrenceBin(t1);
	if(r1 != -1) { t1_in_ant1 = true; sign_t1_ant1 = (r1 == 0)? false : true; }

	// Sign of t0
	short r2;
	if( proofCheck() )
	{
		r2 = w->getAnt2()->hasOccurrenceBin(t0);
		assert(r2 != -1);
		sign_t0_ant2 = (r2 == 0)? false : true;
		assert(sign_t0_ant2 == (!sign_t0_ant1));
	}
	else sign_t0_ant2 = (!sign_t0_ant1);
	// Look for t1
	r2 = w->getAnt2()->hasOccurrenceBin(t1);
	if(r2 != -1) { t1_in_ant2 = true; sign_t1_ant2 = (r2 == 0)? false : true; }

	// t1 found in both antecedents clauses?
	bool t1_in_C2=t1_in_ant1 && t1_in_ant2;

	bool sign_t0_v1;
	// Determine v1 and v2
	ProofNode *v1=NULL,*v2=NULL;
	// Case t1 not in C2
	if(!t1_in_C2)
	{
		if(t1_in_ant1)
		{	v1=w->getAnt1(); sign_t0_v1=sign_t0_ant1; }
		else
		{	v1=w->getAnt2(); sign_t0_v1=sign_t0_ant2; }
		v2=(v1==w->getAnt1()) ? w->getAnt2() : w->getAnt1();
		assert(v1!=v2);
	}
	// Case t1 in C2
	else
	{
		// If t0 in C3 we can determine who is v1 and
		// who is v2 looking at the sign of t0
		// otherwise they are interchangeable
		if(t0_in_C3)
		{
			v1=(sign_t0_ant1==sign_t0_C3) ? w->getAnt1() : w->getAnt2();
			v2=(v1==w->getAnt1()) ? w->getAnt2() : w->getAnt1();
		}
		// As we like
		else
		{	v1=w->getAnt1(); v2=w->getAnt2(); }
	}
	assert(v2);

	//Update applicability info
	ra.cv1=v1->getId();
	ra.cv2=v2->getId();
	ra.cw=w->getId();
	ra.cv3=v3->getId();
	ra.cv=v->getId();

	assert(ra.cv == idv);
	assert(idv == v->getId());
	assert(v == graph[idv]);
	assert(v == graph[ra.cv]);

	//Rules application
	if(!t1_in_C2 && !t0_in_C3)
	{
		//A1 undo case
		if((v3->getAnt1()==v2 || v3->getAnt2()==v2) && (v3->getPivot()==w->getPivot())
				&& (/*v3->getNumResolvents()==1 && */w->getNumResolvents()==1))
			ra.type=rA1prime;
		//A2 leading to B case
		else if(v3->getAnt1()!=NULL && v3->getAnt2()!=NULL && w->getPivot()==v3->getPivot())
			ra.type=rA2B;
		//A2 unary case
		else if(graph[ra.cv2]->getClauseSize()==1)
			ra.type=rA2u;
		else
			ra.type=rA2;
		return true;
	}
	else if(t1_in_C2 && !t0_in_C3)
	{
		if(graph[ra.cv3]->getAnt1()!=NULL && graph[ra.cw]->getPivot()==graph[ra.cv3]->getPivot())
			ra.type=rA1B;
		else
			ra.type=rA1;
		return true;	}
	else if(t1_in_C2 && t0_in_C3)
	{	ra.type=rB1; return true;	}
	else if(!t1_in_C2 && t0_in_C3 && sign_t0_C3==sign_t0_v1)
	{
		if(graph[ra.cv]->getClauseSize()==1)
			ra.type=rB2;
		else
			ra.type=rB2prime;
		return true;
	}
	else if(!t1_in_C2 && t0_in_C3 && sign_t0_C3!=sign_t0_v1)
	{	ra.type=rB3; return true;	}
	else
		//Rules are exhaustive!
	{	opensmt_error("Unknown reduction rule context");	}
	return false;
}

//Given a 5 nodes context, applies the corresponding rule
clauseid_t ProofGraph::ruleApply(RuleContext& ra)
{
	rul_type toApply=ra.getType();
	assert(toApply!=rNO);
	assert(ra.getV1()!=-1);
	clauseid_t claid = 0;

	if(toApply==rA1 || toApply==rA1B) claid = applyRuleA1(ra);
	else if (toApply==rA1prime) applyRuleA1Prime(ra);
	else if(toApply==rA2 || toApply==rA2u || toApply==rA2B) applyRuleA2(ra);
	else if(toApply==rB1) applyRuleB1(ra);
	else if(toApply==rB2prime) applyRuleB2Prime(ra);
	else if(toApply==rB2) applyRuleB2(ra);
	else if(toApply==rB3) applyRuleB3(ra);
	return claid;
}

clauseid_t ProofGraph::applyRuleA1( RuleContext& ra )
{
	assert(getNode(ra.getW())->getNumResolvents()==1);

	//Transformation A1
	//v1 is combined with v3
	//v2 is combined with v3
	//the results are combined together to give v

	ProofNode *v1=getNode(ra.getV1()),*v2=getNode(ra.getV2()),
			*w=getNode(ra.getW()),*v3=getNode(ra.getV3()),*v=getNode(ra.getV());

	assert((v->getAnt1()==w && v->getAnt2()== v3) || (v->getAnt1()==v3 && v->getAnt2()== w));
	assert((w->getAnt1()==v1 && w->getAnt2()== v2) || (w->getAnt1()==v2 && w->getAnt2()==v1));

	//w' given by resolution v1,v3 over v pivot
	mergeClauses(v1->getClause(),v3->getClause(),w->getClause(),v->getPivot());

	assert(w->getAnt1()==v2 || w->getAnt2()==v2);
	if(w->getAnt1()==v2) w->setAnt1(v3); else w->setAnt2(v3);
	v3->remRes(ra.getV());
	v3->addRes(ra.getW());

	//Creation new node y
	ProofNode* y=new ProofNode(logic_);
	y->initClause();
	//y given by resolution v2,v3 over v pivot
	mergeClauses(v2->getClause(),v3->getClause(),y->getClause(),v->getPivot());

	v2->remRes(ra.getW());
	y->setAnt1(v2);
	y->setAnt2(v3);
	y->setType(clause_type::CLA_DERIVED);
	y->setPivot(v->getPivot());
	y->setId(graph.size());
	y->addRes(ra.getV());
	graph.push_back(y);
	v2->addRes(y->getId());
	v3->addRes(y->getId());
	// Return id new node
	clauseid_t claid = y->getId();

	//for(size_t k = 0; k<getGraphSize(); k++) if(getNode(k)!=NULL) assert(getNode(k)->getId()==k);

	//NOTE for interpolation
	if(produceInterpolants()) y->initIData();

	//v pivot becomes w pivot and viceversa
	Var aux;
	aux=w->getPivot(); w->setPivot(v->getPivot()); v->setPivot(aux);
	//v new antecedents are w and y
	if(v->getAnt1()==v3) v->setAnt1(y); else v->setAnt2(y);
	assert( (w->getAnt1()==v1 && w->getAnt2()==v3) || (w->getAnt2()==v1 && w->getAnt1()==v3));
	assert( (v->getAnt1()==y && v->getAnt2()==w) || (v->getAnt2()==y && v->getAnt1()==w));
	A1++;
	return claid;
}

void ProofGraph::applyRuleA1Prime( RuleContext& ra )
{
	assert(getNode(ra.getW())->getNumResolvents()==1);

	//Transformation to undo A1 effect -> factorization
	ProofNode *v1=getNode(ra.getV1()),*v2=getNode(ra.getV2()),
			*w=getNode(ra.getW()),*v3=getNode(ra.getV3()),*v=getNode(ra.getV());

	assert((v->getAnt1()==w && v->getAnt2()== v3) || (v->getAnt1()==v3 && v->getAnt2()== w));
	assert((w->getAnt1()==v1 && w->getAnt2()== v2) || (w->getAnt1()==v2 && w->getAnt2()==v1));
	Var aux;

	ProofNode * newv2 = NULL;
	if(v3->getAnt1()==v2) newv2=v3->getAnt2();
	else if(v3->getAnt2()==v2) newv2=v3->getAnt1();

	assert(v3->getAnt1()==v2 || v3->getAnt2()==v2);

	//Go back to A1 initial configuration
	mergeClauses(v1->getClause(),newv2->getClause(),w->getClause(),v->getPivot());

	//Update antecedents
	w->setAnt1(v1);
	w->setAnt2(newv2);
	v->setAnt1(w);
	v->setAnt2(v2);
	//Swap pivots
	aux=v->getPivot(); v->setPivot(w->getPivot()); w->setPivot(aux);
	//remove v3 if useless
	v2->remRes(ra.getW());
	v2->addRes(ra.getV());
	v3->remRes(ra.getV());
	newv2->addRes(ra.getW()); // Gains w
	assert(v3->getAnt1()->getNumResolvents()>=2 && v3->getAnt2()->getNumResolvents()>=2);
	if(v3->getNumResolvents()==0)
	{
		newv2->remRes(v3->getId());
		v2->remRes(v3->getId());
		removeNode(v3->getId());
	}
	A1prime++;
}

void ProofGraph::applyRuleA2( RuleContext& ra )
{
	assert(getNode(ra.getW())->getNumResolvents()==1);

	//Transformation A2(plain swap)
	//v2 and v3 change place
	//w changes but v doesn't

	ProofNode *v1=getNode(ra.getV1()),*v2=getNode(ra.getV2()),
			*w=getNode(ra.getW()),*v3=getNode(ra.getV3()),*v=getNode(ra.getV());

	assert((v->getAnt1()==w && v->getAnt2()== v3) || (v->getAnt1()==v3 && v->getAnt2()== w));
	assert((w->getAnt1()==v1 && w->getAnt2()== v2) || (w->getAnt1()==v2 && w->getAnt2()==v1));

	//Remove v2 from w antecedents, add v3 to w antecedents
	if(w->getAnt1()==v2) w->setAnt1(v3);
	else w->setAnt2(v3);
	//Remove v3 from v antecedents, add v2 to v antecedents
	if(v->getAnt1()==v3) v->setAnt1(v2);
	else v->setAnt2(v2);

	v2->remRes(ra.getW());
	v2->addRes(ra.getV());
	v3->remRes(ra.getV());
	v3->addRes(ra.getW());

	//Change w clause to resolvent of v1 and v3 over t1 : t0 C1 C3
	mergeClauses(v1->getClause(),v3->getClause(),w->getClause(),v->getPivot());

	//Change pivots w:t0->t1,v:t1->t0;
	Var aux;
	aux=w->getPivot(); w->setPivot(v->getPivot()); v->setPivot(aux);
	A2++;
}

void ProofGraph::applyRuleB1( RuleContext& ra )
{
	//Transformation B1
	//v1 is combined with v3
	//v2 does not contribute anymore
	//w might be removed
	//the new result v' (t0 C1 C3) subsumes v (t0 C1 C2 C3)
	//Must propagate changes

	ProofNode *v1=getNode(ra.getV1()),*v2=getNode(ra.getV2()),
			*w=getNode(ra.getW()),*v3=getNode(ra.getV3()),*v=getNode(ra.getV());

	assert((v->getAnt1()==w && v->getAnt2()== v3) || (v->getAnt1()==v3 && v->getAnt2()== w));
	assert((w->getAnt1()==v1 && w->getAnt2()== v2) || (w->getAnt1()==v2 && w->getAnt2()==v1));

	//v new antecedents are v1 and v3
	if(v->getAnt1()==w) v->setAnt1(v1);
	else v->setAnt2(v1);
	// w loses v as resolvent, v1 gains v as resolvent
	v1->addRes(ra.getV());
	w->remRes(ra.getV());

	//Change v clause to resolvent of v1 and v3 over t1 : t0 C1 C3
	mergeClauses(v1->getClause(),v3->getClause(),v->getClause(),v->getPivot());
	//Remove w, if no more resolvents (and in case also v2, w was its only resolvent)
	if(w->getNumResolvents()==0) removeTree(w->getId());
	B1++;
}

void ProofGraph::applyRuleB2( RuleContext& ra )
{
	assert(getNode(ra.getW())->getNumResolvents()==1);

	//Transformation B2(swap with loss of literal) NB: useful only for B2k!
	//v2 and v3 change place
	//w changes and v loses t0: the new v' (C1 C2 C3) subsumes v (t0 C1 C2 C3)
	//Must propagate changes

	ProofNode *v1=getNode(ra.getV1()),*v2=getNode(ra.getV2()),
			*w=getNode(ra.getW()),*v3=getNode(ra.getV3()),*v=getNode(ra.getV());

	assert((v->getAnt1()==w && v->getAnt2()== v3) || (v->getAnt1()==v3 && v->getAnt2()== w));
	assert((w->getAnt1()==v1 && w->getAnt2()== v2) || (w->getAnt1()==v2 && w->getAnt2()==v1));

	//Remove v2 from w antecedents, add v3 to w antecedents
	if(w->getAnt1()==v2) w->setAnt1(v3);
	else w->setAnt2(v3);
	//Remove v3 from v antecedents, add v2 to v antecedents
	if(v->getAnt1()==v3) v->setAnt1(v2);
	else v->setAnt2(v2);

	v2->remRes(ra.getW());
	v2->addRes(ra.getV());
	v3->remRes(ra.getV());
	v3->addRes(ra.getW());

	//Change w clause to resolvent of v1 and v3 over t1 : t0 C1 C3
	mergeClauses(v1->getClause(),v3->getClause(),w->getClause(),v->getPivot());
	//Change v clause to resolvent of w and v2 over t0 : C1 C2 C3
	mergeClauses(w->getClause(),v2->getClause(),v->getClause(),w->getPivot());

	//Change pivots w:t0->t1,v:t1->t0;
	Var aux;
	aux=w->getPivot();w->setPivot(v->getPivot());v->setPivot(aux);
	B2++;
}

void ProofGraph::applyRuleB2Prime( RuleContext& ra )
{
	//Transformation B2'
	//v1 is combined with v3
	//v2 does not contribute anymore
	//w might be removed
	//the new result v' (t0 C1 C3) subsumes v (t0 C1 C2 C3)
	//Must propagate changes

	ProofNode *v1=getNode(ra.getV1()),*v2=getNode(ra.getV2()),
			*w=getNode(ra.getW()),*v3=getNode(ra.getV3()),*v=getNode(ra.getV());

	assert((v->getAnt1()==w && v->getAnt2()== v3) || (v->getAnt1()==v3 && v->getAnt2()== w));
	assert((w->getAnt1()==v1 && w->getAnt2()== v2) || (w->getAnt1()==v2 && w->getAnt2()==v1));

	//v new antecedents are v1 and v3
	if(v->getAnt1()==w) v->setAnt1(v1);
	else v->setAnt2(v1);
	// w loses v as resolvent, v1 gains v as resolvent
	v1->addRes(ra.getV());
	w->remRes(ra.getV());

	//Change v clause to resolvent of v1 and v3 over t1 : t0 C1 C3
	mergeClauses(v1->getClause(),v3->getClause(),v->getClause(),v->getPivot());
	//Remove w, if no more resolvents (and in case also v2, w was its only resolvent)
	if(w->getNumResolvents()==0) removeTree(w->getId());
	B2prime++;
}

void ProofGraph::applyRuleB3( RuleContext& ra )
{
	//Transformation B3
	//Supercut!!!
	//v1, v3 don't contribute anymore
	//w might be removed
	//v is replaced by v2 and removed
	//the new result v2 (~t0 C2) subsumes v (~t0 C1 C2 C3)
	//Must propagate changes

	ProofNode *v1=getNode(ra.getV1()),*v2=getNode(ra.getV2()),
			*w=getNode(ra.getW()),*v3=getNode(ra.getV3()),*v=getNode(ra.getV());

	assert((v->getAnt1()==w && v->getAnt2()== v3) || (v->getAnt1()==v3 && v->getAnt2()== w));
	assert((w->getAnt1()==v1 && w->getAnt2()== v2) || (w->getAnt1()==v2 && w->getAnt2()==v1));

	if( proofCheck() > 1 )
	{
		for(unsigned u = 0; u < getGraphSize(); u++)
			if(getNode(u) != NULL && !isRoot(getNode(u)) && getNode(u)->getNumResolvents() == 0)
			{
				cerr << u << " detached" << endl;
				opensmt_error_();
			}
	}

	w->remRes( ra.getV() );
	v3->remRes( ra.getV() );
	// v2 inherits v children
	set<clauseid_t>& resolvents = v->getResolvents();
	for(set<clauseid_t>::iterator it = resolvents.begin(); it!=resolvents.end(); it++)
	{
		assert((*it)<getGraphSize());
		ProofNode* res = getNode((*it));
		assert(res!=NULL);
		if(res->getAnt1() == v) res->setAnt1( v2 );
		else if (res->getAnt2() == v) res->setAnt2( v2 );
		else opensmt_error_();
		v2->addRes((*it));
	}
	assert(v->getNumResolvents()>0);

	// w might become useless
	if(w->getNumResolvents()==0)
	{
		v1->remRes( ra.getW() );
		v2->remRes( ra.getW() );
		removeNode( ra.getW() );
		// v1 can become useless
		assert(v2->getNumResolvents()>0);
		if(v1->getNumResolvents()==0) removeTree(v1->getId());
	}
	// v3 can become useless
	if(v3->getNumResolvents()==0) removeTree(v3->getId());
	//Remove v
	removeNode(v->getId());

	/*
	// NOTE rule application in line with other rules, where v stays there
	// alternative: copy content of v2 into v and keep both nodes
	// NOTE We cannot create another leaf!!
	if(v2->getType() == CLAORIG) return;

	v->setAnt1(v2->getAnt1());
	v->setAnt2(v2->getAnt2());
	v->getAnt1()->addRes(v->getId());
	v->getAnt2()->addRes(v->getId());

	v->setPivot(v2->getPivot());
	v->setType(v2->getType());
	v->setClause(v2->getClause());
	assert(v->getNumResolvents()>0); // TODO what if v was the root?

	checkClause(v->getId());

	for(unsigned u = 0; u < getGraphSize(); u++)
		if(getNode(u) != NULL && !isRoot(getNode(u)) && getNode(u)->getNumResolvents() == 0)
		{
			cerr << u << " detached" << endl;
			opensmt_error_();
		}

	// w might become useless
	w->remRes( ra.getV() );
	v3->remRes( ra.getV() );
	if(w->getNumResolvents()==0) removeTree(w->getId());
	// v3 can become useless
	if(v3->getNumResolvents()==0) removeTree(v3->getId());*/

	if( proofCheck() > 1 )
	{
		for(unsigned u = 0; u < getGraphSize(); u++)
			if(getNode(u) != NULL && !isRoot(getNode(u)) && getNode(u)->getNumResolvents() == 0)
			{
				cerr << u << " detached" << endl;
				opensmt_error_();
			}
	}

	B3++;
}

#endif
