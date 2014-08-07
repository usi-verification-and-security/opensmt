/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

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

#include "ProofGraph.h"

#ifdef PRODUCE_PROOF

// Check if a rule can be applied and if so, determine its context
// v3 and v are given in input
// ra is modified to contain the 5 nodes context
// Return false if w has not antecedents (that is, v1 and v2 don't exist)
bool ProofGraph::getApplContext(clauseid_t idv3, clauseid_t idv, RuleContext& ra)
{
  ra.reset();
  ProofNode* v3=graph[idv3];
  ProofNode* v=graph[idv];
#ifdef CHECK
  assert(idv3>=0);
  assert((size_t)idv3<graph.size());
  assert(v3!=NULL);
  assert(idv>=0);
  assert((size_t)idv<graph.size());
  assert(v!=NULL);
  assert(v->getAnt1()==v3 || v->getAnt2()==v3);
#endif
  //Determine w, i.e. second antecedent v
  ProofNode* w=(v3==v->getAnt1()) ? v->getAnt2() : v->getAnt1();
  //If w has no antecedents, we don't go anywhere
  if(w->isLeaf()) return false;

  //Resolution pivots
  Var t0=w->getPivot();
  Var t1=v->getPivot();

  //w antecedents are v1,v2; clauses are (t0 t1 C1) and (~t0 C2)
  //w clause is (t1 C1 C2)
  //v antecedents are w and v3; clauses are w clause and (~t1, C3)
  //v clause is (C1 C2 C3)

  bool found1, found2;
  size_t size;

  //Determine sign of t1 and t0 (if present) in v3
  bool sign_t1_v3=false; bool t0_in_C3=false; bool sign_t0_C3=false;
  Lit l;

  found1=false; found2=false;
  size=v3->getClauseSize();
  for(size_t i=0;i<size;i++)
  {
    l=v3->getClause()[i];
    if(var(l)==t1) { sign_t1_v3=sign(l); found1=true; }
    if(var(l)==t0) { sign_t0_C3=sign(l); t0_in_C3=true; found2=true; }
    if(found1 && found2) break;
  }

  //Check condition: t1 not in C2
  bool t1_in_ant1=false, t1_in_ant2 =false, sign_t0_ant1=false, sign_t0_ant2=false;

  //Check first antecedent of w
  found1=false; found2=false;
  size=w->getAnt1()->getClauseSize();
  for(size_t i=0;i<size;i++)
  {
    l=w->getAnt1()->getClause()[i];
    if(var(l)==t1 && sign(l)!=sign_t1_v3) { t1_in_ant1=true; found1=true; }
    if(var(l)==t0) { sign_t0_ant1= sign(l); found2=true; }
    if(found1 && found2) break;
  }

  //Check second antecedent of w
  found1=false; found2=false;
  size=w->getAnt2()->getClauseSize();
  for(size_t i=0;i<size;i++)
  {
    l=w->getAnt2()->getClause()[i];
    if(var(l)==t1 && sign(l)!=sign_t1_v3) { t1_in_ant2=true; found1=true; }
    if(var(l)==t0) { sign_t0_ant2= sign(l); found2=true; }
    if(found1 && found2) break;
  }

  //t1 found in both antecedents clauses?
  bool t1_in_C2=t1_in_ant1 && t1_in_ant2;

  bool sign_t0_v1;
  //Determine v1 and v2
  ProofNode *v1=NULL,*v2=NULL;
  //Case t1 not in C2
  if(!t1_in_C2)
  {
    if(t1_in_ant1)
    {	v1=w->getAnt1();		sign_t0_v1=sign_t0_ant1;	}
    else
    {	v1=w->getAnt2();		sign_t0_v1=sign_t0_ant2;	}
    v2=(v1==w->getAnt1()) ? w->getAnt2() : w->getAnt1();
#ifdef CHECK
    assert(v1!=v2);
#endif
  }
  //Case t1 in C2
  else
  {
    //If t0 in C3 we can determine who is v1 and
    //who is v2 looking at the sign of t0
    //otherwise they are interchangeable
    if(t0_in_C3)
    {
      v1=(sign_t0_ant1==sign_t0_C3) ? w->getAnt1() : w->getAnt2();
      v2=(v1==w->getAnt1()) ? w->getAnt2() : w->getAnt1();
    }
    //BOH!
    else
    {	v1=w->getAnt1();		v2=w->getAnt2();		}
  }
#ifdef CHECK
  assert(v2!=NULL);
#endif
  //Update applicability info
  ra.cv1=v1->getId();
  ra.cv2=v2->getId();
  ra.cw=w->getId();
  ra.cv3=v3->getId();
  ra.cv=v->getId();

#ifdef CHECK
  assert(ra.cv == idv);
  assert(idv == v->getId());
  assert(v == graph[idv]);
  assert(v == graph[ra.cv]);
#endif

  //Rules application
  if(!t1_in_C2 && !t0_in_C3)
  {
    //A1 undo case
    if((v3->getAnt1()==v2 || v3->getAnt2()==v2) && (v3->getPivot()==w->getPivot()) && (v3->getNumResolvents()==1 && w->getNumResolvents()==1))
      ra.type=rA1undo;
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
    	ra.type=rB2k;
    else
    	ra.type=rB2;
    return true;
  }
  else if(!t1_in_C2 && t0_in_C3 && sign_t0_C3!=sign_t0_v1)
  {	ra.type=rB3; return true;	}
  else
    //Rules are exhaustive!
  {	ra.type=rNO; assert(false);	}
  return false;
}

//Given a 5 nodes context, applies the corresponding rule
bool ProofGraph::ruleApply(RuleContext& ra)
{
  rul_type toApply=ra.type;
#ifdef CHECK
  assert(toApply!=rNO);
#endif

  //Check if duplication allowed and in case do it
  if(graph[ra.cw]->getNumResolvents()>1)
    dupliClause(ra.cw,ra.cv);

#ifdef CHECK
  assert(graph[ra.cw]->getNumResolvents()==1);
#endif

  //Transformation A1
  //v1 is combined with v3
  //v2 is combined with v3
  //the results are combined together to give v
  if(toApply==rA1 || toApply==rA1B)
  {
    ProofNode *v1=graph[ra.cv1],*v2=graph[ra.cv2],*w=graph[ra.cw],*v3=graph[ra.cv3],*v=graph[ra.cv];
    //w' given by resolution v1,v3 over v pivot
    mergeClauses(v1->getClause(),v3->getClause(),w->getClause(),v->getPivot());

    w->setAnt1(v1);
    w->setAnt2(v3);

    //Creation new node y
    ProofNode* y=new ProofNode();
    //y given by resolution v2,v3 over v pivot
    mergeClauses(v2->getClause(),v3->getClause(),y->getClause(),v->getPivot());

    y->setAnt1(v2);
    y->setAnt2(v3);
    y->addResolvent(v);
    y->setType(CLALEARNT);
    y->setPivot(v->getPivot());
    y->setId(graph.size());
    graph.push_back(y);

    if(graph.size()>SIZE_BIT_VECTOR)
    {
      cerr << "GRAPH TOO LARGE" << endl;
      assert(false);
    }

    //v3 loses v and gains w,y
    v3->removeResolvent(v);
    v3->addResolvent(y);
    v3->addResolvent(w);
    //v2 loses w and gains y
    v2->removeResolvent(w);
    v2->addResolvent(y);

    //v pivot becomes w pivot and viceversa
    Var aux;
    aux=w->getPivot(); w->setPivot(v->getPivot()); v->setPivot(aux);
    //v new antecedents are w and y
    v->setAnt1(w);
    v->setAnt2(y);

    if(toApply==rA1)
      A1++;
    else
      A1B++;
    num_node_add_A1++;
  }

  //Transformation to undo A1 effect -> factorization
  else if (toApply==rA1undo)
  {
    ProofNode *v1=graph[ra.cv1],*v2=graph[ra.cv2],*w=graph[ra.cw],*v3=graph[ra.cv3],*v=graph[ra.cv];
    Var aux;

    ProofNode * newv2 = NULL;
    if(v3->getAnt1()==v2) newv2=v3->getAnt2();
    else if(v3->getAnt2()==v2) newv2=v3->getAnt1();

    assert(v3->getAnt1()==v2 || v3->getAnt2()==v2);
    assert(w->getNumResolvents()==1);
    assert(v3->getNumResolvents()==1);

    //Go back to A1 initial configuration
    mergeClauses(v1->getClause(),newv2->getClause(),w->getClause(),v->getPivot());

    //v2 loses v3 and w and gains v
    v2->removeResolvent(v3);
    v2->removeResolvent(w);
    v2->addResolvent(v);
    //newv2 loses v3 and gains w
    newv2->removeResolvent(v3);
    newv2->addResolvent(w);
    //Update antecedents
    w->setAnt1(v1);
    w->setAnt2(newv2);
    v->setAnt1(w);
    v->setAnt2(v2);
    //Swap pivots
    aux=v->getPivot(); v->setPivot(w->getPivot()); w->setPivot(aux);
    //remove v3
    removeNode(v3->getId());
    A1Undo++;
  }
  //Transformation A2(plain swap)
  //v2 and v3 change place
  //w changes but v doesn't
  else if(toApply==rA2 || toApply==rA2u || toApply==rA2B)
  {
    ProofNode *v1=graph[ra.cv1],*v2=graph[ra.cv2],*w=graph[ra.cw],*v3=graph[ra.cv3],*v=graph[ra.cv];
    //Remove w from v2 resolvents
    //Add v to v2 resolvents
    v2->removeResolvent(w);
    v2->addResolvent(v);
    //Remove v from v3 resolvents
    //Add w to v3 resolvents
    v3->removeResolvent(v);
    v3->addResolvent(w);
    //Remove v2 from w antecedents, add v3 to w antecedents
    if(w->getAnt1()==v2) w->setAnt1(v3);
    else w->setAnt2(v3);
    //Remove v3 from v antecedents, add v2 to v antecedents
    if(v->getAnt1()==v3) v->setAnt1(v2);
    else v->setAnt2(v2);

    //Change w clause to resolvent of v1 and v3 over t1 : t0 C1 C3
    mergeClauses(v1->getClause(),v3->getClause(),w->getClause(),v->getPivot());

    //Change pivots w:t0->t1,v:t1->t0;
    Var aux;
    aux=w->getPivot(); w->setPivot(v->getPivot()); v->setPivot(aux);

    if(toApply==rA2u)
      A2U++;
    else if(toApply==rA2)
      A2++;
    else
      A2B++;
  }

  //Transformation B1 or B2
  //v1 is combined with v3
  //v2 does not contribute anymore
  //w is removed
  //the new result v' (t0 C1 C3) subsumes v (t0 C1 C2 C3)
  //Must propagate changes
  //TODO remove v2 subtree if needed
  else if(toApply==rB1 || toApply==rB2)
  {
    ProofNode *v1=graph[ra.cv1],*v2=graph[ra.cv2],*w=graph[ra.cw],*v3=graph[ra.cv3],*v=graph[ra.cv];
    //v1 loses w and gains v
    v1->removeResolvent(w);
    v1->addResolvent(v);
    //v2 loses w
    v2->removeResolvent(w);
    //v new antecedents are v1 and v3
    v->setAnt1(v1);
    v->setAnt2(v3);

    //Change v clause to resolvent of v1 and v3 over t1 : t0 C1 C3
    mergeClauses(v1->getClause(),v3->getClause(),v->getClause(),v->getPivot());

    //Remove w
    removeNode(w->id);

    if(toApply==rB1)
      B1++;
    else
      B2++;

    //v2 becomes useless
    if(v2->getNumResolvents()==0) removeTree(v2->getId());
  }

  //Transformation B2(swap with loss of literal) NB: useful only for B2k!
  //v2 and v3 change place
  //w changes and v loses t0: the new v' (C1 C2 C3) subsumes v (t0 C1 C2 C3)
  //Must propagate changes
  else if(toApply==rB2k)
  {
    ProofNode *v1=graph[ra.cv1],*v2=graph[ra.cv2],*w=graph[ra.cw],*v3=graph[ra.cv3],*v=graph[ra.cv];
    //Remove w from v2 resolvents
    //Add v to v2 resolvents
    v2->removeResolvent(w);
    v2->addResolvent(v);
    //Remove v from v3 resolvents
    //Add w to v3 resolvents
    v3->removeResolvent(v);
    v3->addResolvent(w);
    //Remove v2 from w antecedents, add v3 to w antecedents
    if(w->getAnt1()==v2) w->setAnt1(v3);
    else w->setAnt2(v3);
    //Remove v3 from v antecedents, add v2 to v antecedents
    if(v->getAnt1()==v3) v->setAnt1(v2);
    else v->setAnt2(v2);

    //Change w clause to resolvent of v1 and v3 over t1 : t0 C1 C3
    mergeClauses(v1->getClause(),v3->getClause(),w->getClause(),v->getPivot());

    //Change v clause to resolvent of w and v2 over t0 : C1 C2 C3
    mergeClauses(w->getClause(),v2->getClause(),v->getClause(),w->getPivot());

    //Change pivots w:t0->t1,v:t1->t0;
    Var aux;
    aux=w->getPivot();w->setPivot(v->getPivot());v->setPivot(aux);

    if(toApply==rB2k)
      B2K++;
  }

  //Transformation B3
  //Supercut!!!
  //v1, v3 don't contribute anymore
  //w is removed
  //v is replaced by v2 and removed
  //the new result v2 (~t0 C2) subsumes v (~t0 C1 C2 C3)
  //Must propagate changes
  //TODO remove v1,v3 subtrees if needed
  else if(toApply==rB3)
  {
    ProofNode *v1=graph[ra.cv1],*v2=graph[ra.cv2],*w=graph[ra.cw],*v3=graph[ra.cv3],*v=graph[ra.cv];
    //v2 loses w
    v2->removeResolvent(w);
    //v1 loses w
    v1->removeResolvent(w);
    //v3 loses v
    v3->removeResolvent(v);
    //Update v resolvents
    for(set<ProofNode*>::iterator it=v->getResolvents().begin(); it!=v->getResolvents().end(); it++)
    {
      //Resolvent is gained by v2
      v2->addResolvent((*it));
      //Remove v from n antecedents, add v2 to n antecedents
      if((*it)->getAnt1()==v) (*it)->setAnt1(v2);
      else (*it)->setAnt2(v2);
    }

    //Remove v,w
    removeNode(v->getId());
    removeNode(w->getId());
    B3++;

    // v1, v3 become useless
    if(v1->getNumResolvents()==0) removeTree(v1->getId());
    if(v3->getNumResolvents()==0) removeTree(v3->getId());
  }
  else assert(false);

  return true;
}

#endif
