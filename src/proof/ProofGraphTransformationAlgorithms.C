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

//************************* RECYCLE PIVOTS AND RECYCLE UNITS ***************************

double ProofGraph::recyclePivotsIter()
{
  double initTime=cpuTime();
  clauseid_t c;
  vector<clauseid_t> q;

  int currPosition;
  Var targetPiv,curPiv;
  ProofNode * targetNode      = NULL
    , * curNode         = NULL
    , * curNodeOtherAnt = NULL;

  bool curNodeOtherAntPol = false
    , targetNodeAnt1Pol  = false
    , cutAnt1            = false
    , replaced           = false
    , found1             = false
    , found2             = false;

  q.push_back(root);
  do
  {
    c=q.back();
    targetNode=graph[c];
    assert(targetNode!=NULL);
    replaced=false;

    //Node not visited yet
    //NB nodes visited only once on a single incoming path from sink
    if(!visited[c])
    {
      visited[c]=true;

      //Both antecedents present
      //Target node can be substituted only if it has one resolvent
      if((!targetNode->isLeaf()) && (targetNode->getNumResolvents()==1))
      {
#ifdef CHECK
	assert(graph[targetNode->ant1->id]!=NULL);
	assert(graph[targetNode->ant2->id]!=NULL);
#endif
	//Look for current node pivot along the path to the sink
	//stop if found node with same pivot or multiple resolvents
	targetPiv=targetNode->getPivot();
	//Start from node before the current one
	currPosition=q.size()-2;
	while(currPosition>=0 && !replaced)
	{
	  curNode=graph[q[currPosition]];
	  assert(curNode!=NULL);
	  assert( (curNode->getAnt1()==graph[q[currPosition+1]]) || (curNode->getAnt2()==graph[q[currPosition+1]]) );
	  curPiv=curNode->getPivot();
	  //Found pivot redundancy
	  if(curPiv==targetPiv)
	  {
	    found1=false;
	    //Check polarity pivot in target node antecedents
	    for(size_t k=0;k<targetNode->getAnt1()->getClauseSize();k++)
	      if(var(targetNode->getAnt1()->getClause()[k])==curPiv)
	      {
		if(sign(targetNode->getAnt1()->getClause()[k]))
		  targetNodeAnt1Pol=false;
		else if(!(sign(targetNode->getAnt1()->getClause()[k])))
		  targetNodeAnt1Pol=true;
		else assert(false);
		found1=true;
		break;
	      }
	    if(!found1)assert(false);

	    //Determine current node antecedent not in current path
	    if(curNode->getAnt1() == graph[q[currPosition+1]])
	      curNodeOtherAnt=curNode->getAnt2();
	    else if(curNode->getAnt2() == graph[q[currPosition+1]])
	      curNodeOtherAnt=curNode->getAnt1();
	    else assert(false);
#ifdef CHECK
	    assert(curNode->ant1!=NULL);
	    assert(curNode->ant2!=NULL);
	    assert(graph[curNodeOtherAnt->id]!=NULL);
#endif

	    found2=false;
	    //Check polarity pivot in current node antecedent not in current path
	    for(size_t k=0;k<curNodeOtherAnt->getClauseSize();k++)
	      if(var(curNodeOtherAnt->getClause()[k])==curPiv)
	      {
		if(sign(curNodeOtherAnt->getClause()[k]))
		  curNodeOtherAntPol=false;
		else if(!(sign(curNodeOtherAnt->getClause()[k])))
		  curNodeOtherAntPol=true;
		else assert(false);
		found2=true;
		break;
	      }
	    if(!found2)
	    {
	      cout << "No more pivot for " << curNodeOtherAnt->getId() << " antecedent of "<< curNode->getId() << endl;
	      assert(false);
	    }

	    //NB a node st not both antecedents have its pivot
	    //is doomed to be substituted by the antecedent without pivot!
	    if(true/*found1 && found2*/)
	    {
	      replaced=true;

	      //Cut the proper target node antecedent
	      if(targetNodeAnt1Pol==curNodeOtherAntPol)
		cutAnt1=true;
	      else
		cutAnt1=false;

	      //ant1 loses n
	      targetNode->getAnt1()->removeResolvent(targetNode);
	      //ant2 loses n
	      targetNode->getAnt2()->removeResolvent(targetNode);
	      if(cutAnt1)
	      {
		//Ant2 substitutes node
		for(set<ProofNode*>::iterator it=targetNode->getResolvents().begin(); it!=targetNode->getResolvents().end(); it++)
		{
		  //Ant2 gains n resolvents
		  targetNode->getAnt2()->addResolvent((*it));

		  //Remove n from n resolvents antecedents, add ant2
		  if((*it)->getAnt1()==targetNode) (*it)->setAnt1(targetNode->getAnt2());
		  else if((*it)->getAnt2()==targetNode) (*it)->setAnt2(targetNode->getAnt2());
		  else assert(false);
		}
		targetNode->getResolvents().clear();
		//Remove ant1 if it has no more resolvents
		if(targetNode->getAnt1()->getNumResolvents()==0) { removeTree(targetNode->getAnt1()->getId()); targetNode->setAnt1(NULL); }

	      }
	      else
	      {
		//Ant1 substitutes node
		for(set<ProofNode*>::iterator it=targetNode->getResolvents().begin(); it!=targetNode->getResolvents().end(); it++)
		{
		  //ant1 gains n resolvents
		  targetNode->getAnt1()->addResolvent((*it));

		  //Remove n from n resolvents antecedents, add ant1
		  if((*it)->getAnt1()==targetNode) (*it)->setAnt1(targetNode->getAnt1());
		  else if((*it)->getAnt2()==targetNode) (*it)->setAnt2(targetNode->getAnt1());
		  else assert(false);
		}
		targetNode->getResolvents().clear();
		//Remove ant2 if it has no more resolvents
		if(targetNode->getAnt2()->getResolvents().size()==0) { removeTree(targetNode->getAnt2()->getId()); targetNode->setAnt2(NULL); }

	      }
	    }
	  }
	  //Stop loop if current node has multiple resolvents
	  if(graph[q[currPosition]]->getNumResolvents()>1)
	    break;
	  else currPosition--;
	}
      }
    }

    //If node visited, pivot found and cut done, replace current node on stack with the substituting antecedent
    if(replaced)
    {
      q.pop_back();
      if(cutAnt1)
	q.push_back(targetNode->getAnt2()->getId());
      else
	q.push_back(targetNode->getAnt1()->getId());
      removeNode(targetNode->getId());
    }
    //Otherwise visit antecedents
    else
    {
      //If pivot not found enqueue antecedents if not visited
      if(targetNode->getAnt1()!=NULL && !visited[targetNode->getAnt1()->getId()])
	q.push_back(targetNode->getAnt1()->getId());
      else if(targetNode->getAnt2()!=NULL && !visited[targetNode->getAnt2()->getId()])
	q.push_back(targetNode->getAnt2()->getId());
      //Remove node if no antecedents or both antecedents already visited
      else
	q.pop_back();
    }
  }
  while(!q.empty());

  visited.reset();

  double endTime=cpuTime();

  /*	if ( verbose() )
	{
	cout << "# " << "Recycle pivots done" << endl;
	}*/
  return (endTime-initTime);
}


//TODO
/*bool ProofGraph::recycleUnit(clauseid_t cid)
  {
#ifdef CHECK
assert(graph[cid]!=NULL);
assert(graph[cid]->clause.size()==1);
#endif

ProofNode* v;
clauseid_t c;
Var unaryVar;
bool signUnary;
std::deque<clauseid_t> q;
bool succ=false;

//Mark recursive antecedents of this derived unary
q.push_back(cid);
do
{
c=q.front();
v=graph[c];
q.pop_front();
if(!visited3[c])
{
visited3[c]=true;
if(v->ant1!=NULL && v->ant2!=NULL)
{
q.push_back(v->ant1->id);
q.push_back(v->ant2->id);
}
}
}
while(!q.empty());

unaryVar=var(graph[cid]->clause[0]);
signUnary=sign(graph[cid]->clause[0]);

//cout << "Working with unary clause " << cid << " with variable " << unaryVar << endl;

//Modify all the non marked non leaf nodes st pivot is the unary
//Bottom up strategy to cut as soon as possible
q.push_back(sink);
do
{
c=q.front();
v=graph[c];
q.pop_front();
#ifdef CHECK
assert(v!=NULL);
#endif
if(!visited4[c])
{
visited4[c]=true;
//Node is not antecedent of cid, has pivot=cid and does not derive from cid
if(!visited3[c] && v->ant1!=NULL && v->ant2!=NULL)
{
//cout << "Visiting " << c << " with pivot " << v->pivot << endl;

if(v->pivot==unaryVar && v->ant1->id!=cid && v->ant2->id!=cid)
{
//Modify antecedents
if(signUnary==true)
{
//cout << "Substituting " << v->ant1->id << " with " << cid << endl;
//Remove j from ant 1 resolvents
v->ant1->res.erase(v);
//Check if ant1 has no more resolvents
if(v->ant1->res.size()==0) removeTree(v->ant1->id);
//Update j antecedent
v->ant1=graph[cid];
//Add j to cid resolvents
graph[cid]->res.insert(v);
succ=true;
}
else if(signUnary==false)
{
  //cout << "Substituting " << v->ant2->id << " with " << cid << endl;
  //Remove j from ant2 resolvents
  v->ant2->res.erase(v);
  //Check if ant2 has no more resolvents
  if(v->ant2->res.size()==0) removeTree(v->ant2->id);
  //Update j antecedent
  v->ant2=graph[cid];
  //Add j to cid resolvents
  graph[cid]->res.insert(v);
  succ=true;
}
#ifdef CHECK
assert(v->ant1!=NULL);
assert(v->ant2!=NULL);
#endif
//Update clause
#ifdef TRACK_UNARY
if(v->clause.size()==1) unary.erase(v->id);
#endif
mergeClauses(v->ant1->clause, v->ant2->clause, v->clause, v->pivot);
#ifdef TRACK_UNARY
if(v->clause.size()==1) unary.insert(v->id);
#endif
//Propagate changes towards the bottom
//NB this call affects the bitset visited1/2 and reachable
subsumProp(v->id);
}
//If c is antecedent of cid, his antecedents are antecedent of cid themselves
q.push_back(v->ant1->id);
q.push_back(v->ant2->id);
}
}
}
while(!q.empty());

visited3.reset();
visited4.reset();
#ifdef CHECK
checkProof();
#endif
return succ;
}

//TODO improve strategy
void ProofGraph::recycleChainUnits()
{
  set<clauseid_t>::iterator it=unary.begin();
  clauseid_t c;

  do
  {
    c=(*it);
    if(graph[c]!=NULL)
    {
#ifdef CHECK
      assert(graph[c]->clause.size()==1);
#endif
      //TODO at the moment we go back to the start if the recycling is successful
      if(recycleUnitMine(c))
	it=unary.begin();
      else
	it++;
    }
  }
  while(it!=unary.end());
}

*/

//************************ REDUCTION AND PIVOT REORDERING *******************************

//Iterative process:
// 1)Topological visit
// 2)Trasformations and restructuring top-down
//
//Input: available time for transformation, flag to enable transformations, maximum number of transformation loops,
//       flag to delay duplications in swap rules if reordering for interpolation
void ProofGraph::transformAndRestructureOnTheFly(const double left_time, const bool transf, const int max_num_loops)
{
  //assert(!(max_num_loops==-1 && left_time==-1)); Meaningful only for reduction
  assert(!(max_num_loops>0 && left_time>0));
  //Flag to check if in a loop at least a transformation has been applied
  bool some_transf_done;
  long curr_num_loops=0;

  //Allow duplication in swap and cut rules
  bool dupl_allowed_swap = false;
  bool dupl_allowed_cut = true;
  //Try to avoid duplications for swap rules until possible
  //Useful especially for reordering in interpolation
  const bool less_dupl_mode=false;
  if(less_dupl_mode) dupl_allowed_swap=false;

  //Swap and cut rules application criteria
  bool (ProofGraph::*swap_rules_application_criterion)(RuleContext&, bool);
  if( reorderPivots() > 0 )
  {
	  // A rules for reordering
	  swap_rules_application_criterion = &ProofGraph::ARulesInterpolationApplicationCriterionWeak;
	  dupl_allowed_swap = true;
  }
  else
	  // A rules for reduction
	  swap_rules_application_criterion = &ProofGraph::allowSwapRule;
  // Perform cut rules both in reordering and reduction
  bool (ProofGraph::*cut_rules_application_criterion)(RuleContext&, bool)=&ProofGraph::allowCutRule;

  double spent_time=0;
  //Flag to avoid unnecessary updates; activate it after first loop which is assumed to be aimed
  //at reconstruction
  bool avoid_update=false;
  //Main external loop
  do
  {
    some_transf_done=false;

#if ENABLE_SAFE_VARIABLES
    // Calculate safe variables sets to avoid duplications while increasing reduction
    calcSafeVarsSets();
#endif
    //Perform one transformation loop
    spent_time+= doTransformationLoop(some_transf_done, swap_rules_application_criterion, cut_rules_application_criterion,
	dupl_allowed_swap, dupl_allowed_cut, transf, avoid_update);

    curr_num_loops++;
    avoid_update=true;

    if(less_dupl_mode)
    {
      //Flag for the modality "no duplications until necessary" in reordering for interpolation
      //If no transformations done without duplications, try enabling duplications
      if(!dupl_allowed_swap && !some_transf_done){ some_transf_done=true; dupl_allowed_swap=true; }
      //If transformations done with duplications, try disabling duplications
      else if(dupl_allowed_swap && some_transf_done){ dupl_allowed_swap=false; }
    }

  }
  //Continue until
  // - max number of loops reached or timeout (in case of reduction)
  // - some transformation is done (in case of pivot reordering)
  while((max_num_loops==-1? true : curr_num_loops<max_num_loops) &&
		(left_time==-1? true : spent_time<=left_time)			 &&
		(left_time!=-1 || max_num_loops!= -1 || some_transf_done));

  if ( verbose() )
  {
    if(transf)
      cout << "# " << "Graph traversals done: " << curr_num_loops << endl;
    else
      cout << "# " << "Restructuring done" << endl;
  }
}

//Input: flag to enable clause duplications in application rules, flag to enable application rules (if flag false only restructuring done),
//flag to avoid unnecessary clause updates
//Output: returns time spent transforming, flag true if some transformations done
//NB: using here visited vector to keep track of clauses to be updated
double ProofGraph::doTransformationLoop(bool& some_transf_done,
    bool(ProofGraph::*allowSwap)(RuleContext& ra, bool duplAll), bool(ProofGraph::*allowCut)(RuleContext& ra, bool duplAll),
    bool dupl_allowed_swap, bool dupl_allowed_cut, bool apply_rules, bool avoid_update )
{
  double init_time;
  double end_time;
  RuleContext ra1,ra2;
  //Queue for visit and propagation
  std::deque<clauseid_t> q;
  ProofNode* n;
  bool choose_ant1;
  int num_rules_applied=0;
  set<ProofNode*>::iterator it;
  //DFS vector
  vector<clauseid_t> DFSvec;
  //NB unfortunately it is necessary to update sorting each time
  topolSortingVec(DFSvec);

  //Swap rules application criterion
  bool (ProofGraph::*swap_rules_application_criterion)(RuleContext&, bool)=allowSwap;
  bool (ProofGraph::*cut_rules_application_criterion)(RuleContext&, bool)=allowCut;

  init_time=cpuTime();

  long count1=0,count2=0;

  some_transf_done=false;
  //Visit in topological order (while applying transformations)
  for(size_t i=0; i< DFSvec.size(); i++)
  {
    n=graph[DFSvec[i]];

    //A node can have been removed before visit
    if(n==NULL)
    {}
    else
    {
      //Non leaf node
      if(!(n->isLeaf()))
      {
	//Look for pivot in antecedents
	bool piv_in_ant1=false, piv_in_ant2=false;

	for(size_t i=0;i<n->getAnt1()->getClause().size();i++)
	  if(var(n->getAnt1()->getClause()[i])==n->getPivot())
	  { piv_in_ant1=true; break; }
	for(size_t i=0;i<n->getAnt2()->getClause().size();i++)
	  if(var(n->getAnt2()->getClause()[i])==n->getPivot())
	  { piv_in_ant2=true; break; }

	//Easy case: pivot still in both antecedents
	//Sufficient to propagate modifications via merge
	if(piv_in_ant1 && piv_in_ant2)
	{
	  count1++;
	  if(avoid_update)
	  {
	    //Update clause only if necessary
	    if(visited[n->getId()])
	    {
	      count2++;
	      mergeClauses(n->getAnt1()->getClause(),n->getAnt2()->getClause(),n->getClause(),n->getPivot());
	      //Mark resolvents to be updated
	      for(it=n->getResolvents().begin(); it!=n->getResolvents().end(); it++)
		visited[(*it)->getId()]=true;
	    }
	  }
	  else
	    mergeClauses(n->getAnt1()->getClause(),n->getAnt2()->getClause(),n->getClause(),n->getPivot());

#ifdef CHECK
	  checkClause(n->getId());
#endif

	  //This block is done only if transformations are enabled
	  if(apply_rules)
	  {
	    //Look for rules applicability
	    getApplContext(n->getAnt1()->getId(),n->getId(),ra1);
	    getApplContext(n->getAnt2()->getId(),n->getId(),ra2);

	    short chosen = handleRuleApplication(ra1,ra2,swap_rules_application_criterion,cut_rules_application_criterion,
		dupl_allowed_swap,dupl_allowed_cut);

	    if( chosen!=0 )
	    {
	      if(avoid_update)
	      {
		//v changes only in case of B rules:
		//for B1,B2,B2k clause is updated;
		//for B3 node is replaced by v2, which gets its resolvents
		//Must propagate change to resolvents
		if(!((chosen==1 && isSwapRule(ra1.type) && ra1.type!=rB2k) ||
		      (chosen==2 && isSwapRule(ra2.type) && ra2.type!=rB2k)))
		  for(it=n->getResolvents().begin(); it!=n->getResolvents().end(); it++)
		    visited[(*it)->getId()]=true;
	      }

	      if(chosen==1)
		ruleApply(ra1);
	      else if(chosen==2)
		ruleApply(ra2);
	      some_transf_done=true;
	      num_rules_applied++;
	    }
	  }
	  n->setNumNodesSubproof( n->getAnt1()->getNumNodesSubproof() + n->getAnt2()->getNumNodesSubproof() + 1 );
	}
	//Second case: pivot not in ant1 or not in ant2
	//Remove resolution step, remove n, ant without pivots gains n resolvents
	else if(!piv_in_ant1 ||  !piv_in_ant2)
	{
	  //Pivot not in ant1 and not in ant2
	  if(!piv_in_ant1 && !piv_in_ant2)
	  {
	    // TODO Define heuristic to choose one of the two antecedents
	    //1) If an antecedent has only one resolvent, choose the other
	    //2) If both have only one resolvent, choose the smaller clause
	    //3) Break ties randomly

	    if(n->getAnt1()->getNumResolvents()==1 && n->getAnt2()->getNumResolvents()>1)
	      choose_ant1=false;
	    else if(n->getAnt1()->getNumResolvents()>1 && n->getAnt2()->getNumResolvents()==1)
	      choose_ant1=true;
	    else
	    {
	      if(n->getAnt1()->getClauseSize()> n->getAnt2()->getClauseSize())
		choose_ant1=false;
	      else if(n->getAnt2()->getClauseSize()> n->getAnt1()->getClauseSize())
		choose_ant1=true;
	      else
	      {
		if(rand()%2==0)choose_ant1=true; else choose_ant1=false;
	      }
	    }
	  }
	  //Pivot not in ant1
	  else if(!piv_in_ant1 && piv_in_ant2)
	    choose_ant1=true;
	  //Pivot not in ant2
	  else if(piv_in_ant1 && !piv_in_ant2)
	    choose_ant1=false;
	  else assert(false);

	  //ant1 loses n
	  n->getAnt1()->removeResolvent(n);
	  //ant2 loses n
	  n->getAnt2()->removeResolvent(n);

	  if(choose_ant1)
	  {
	    for(it=n->getResolvents().begin(); it!=n->getResolvents().end(); it++)
	    {
	      //ant1 gains n resolvents
	      n->getAnt1()->addResolvent((*it));

	      //Remove n from n resolvents antecedents, add ant1
	      if((*it)->getAnt1()==n) (*it)->setAnt1(n->getAnt1());
	      else if((*it)->getAnt2()==n) (*it)->setAnt2(n->getAnt1());
	      else assert(false);

	      if(avoid_update)
	      {
		//Ant has changed for ex n resolvent, that must be updated
		visited[(*it)->id]=true;
	      }
	    }
	    n->getResolvents().clear();

	  }
	  else if(!choose_ant1)
	  {
	    for(it=n->getResolvents().begin(); it!=n->getResolvents().end(); it++)
	    {
	      //ant2 gains n resolvents
	      n->getAnt2()->addResolvent((*it));

	      //Remove n from n resolvents antecedents, add ant2
	      if((*it)->getAnt1()==n) (*it)->setAnt1(n->getAnt2());
	      else if((*it)->getAnt2()==n) (*it)->setAnt2(n->getAnt2());
	      else assert(false);

	      if(avoid_update)
	      {
		//Ant has changed for ex n resolvent, that must be updated
		visited[(*it)->id]=true;
	      }
	    }
	    n->getResolvents().clear();
	  }

	  //We might have reached old sink
	  //Case legal only if we have produced another empty clause

	  //Cut away trees not contributing anymore
	  //Remove ant2 if it has no more resolvents
	  if(!piv_in_ant1 && n->getAnt2()->getNumResolvents()==0)
	  {removeTree(n->getAnt2()->getId()); n->setAnt2(NULL);}
	  //Remove ant1 if it has no more resolvents
	  if(!piv_in_ant2 && n->getAnt1()->getNumResolvents()==0)
	  {removeTree(n->getAnt1()->getId()); n->setAnt1(NULL);}

	  //Substitute old sink with new
	  if(n->getId()==root)
	  {
	    if(!piv_in_ant1 && n->getAnt1()->getClauseSize()==0) root=n->getAnt1()->getId();
	    if(!piv_in_ant2 && n->getAnt2()->getClauseSize()==0) root=n->getAnt2()->getId();
	  }
	  //remove n
	  removeNode(n->getId());
	}
      }
      else n->setNumNodesSubproof( 1 );
    }
  }
  if(avoid_update)
    visited.reset();

  //cout << "Num potential merge " << count1 << " effective " << count2 << endl;

  end_time=cpuTime()-init_time;

  return end_time;
}

//Work on proof graph keeping it as tree (only A1 rules require re-treefication)
//Alternate RP (with reconstruction) and random A rule application that introduces a redundancy
//TODO might look for a strategy that starts from leaves to keep A1 effect small
//TODO might do some A together and then one recycling
void ProofGraph::alternateARulesRecyclePivots(const double time_limit)
{
  ProofNode* n;
  size_t clause_num;
  int num_rule_applications=0;
  bool isswap;
  // bool done;
  rul_type t;
  RuleContext ra;
  double init_time=cpuTime();

  //Initial treefication of the proof graph
  treefyProofGraph();
  checkTreefication();

  bool A1_applied=false;
  bool A_applied;

  do
  {
    //Perform RecyclePivots
    recyclePivotsIter();
    //Do proof reconstruction
    //doTransformationLoop(done,&ProofGraph::trivialApplicationCriterion,true,false,false);

    checkTreefication();
    checkProof();

    A_applied=false;
    A1_applied=false;
    //Choose random clause and apply A rule to expose redundancy
    do
    {
      clause_num = rand() % graph.size();
      assert(clause_num < graph.size());
      n=graph[clause_num];

      if(n!=NULL && n->getNumResolvents()!=0)
      {
	//Look for rules applicability: context determined by edge n -> unique resolvent of n
	if(getApplContext(n->getId(),(*n->getResolvents().begin())->getId(),ra))
	{
	  t=ra.type;
	  //TODO check automatic cut by A1undo!!!
	  isswap=(t==rA1 || t==rA1B || t==rA1undo || t==rA2 || t==rA2B || t==rA2u);
	  assert(isswap);

	  if(t!=rA1 && t!=rA1B)
	  {
	    //Apply A rule
	    ruleApply(ra);
	    A_applied=true;

	    //Restore proof tree if A1 applied
	    treefyProofGraph();
	    checkTreefication();
	    checkProof();

	    num_rule_applications++;
	  }
	}
      }
    }
    while(!A_applied && (cpuTime() - init_time) <= time_limit);
  }
  while((cpuTime() - init_time) <= time_limit);
}


// Applies one rule randomly looking at the nodes vector and
// if necessary rebuilds the proof
// Output: true if a B rule was applied, false otherwise
void ProofGraph::applyRandomRule()
{
  ProofNode* n;
  size_t clause_num;
  RuleContext ra1, ra2;
  bool rule_applied=false;
  bool done=false;
  //Swap and cut rules application criteria
  bool (ProofGraph::*swap_rules_application_criterion)(RuleContext&, bool)=&ProofGraph::allowRuleInterpolation;
  bool (ProofGraph::*cut_rules_application_criterion)(RuleContext&, bool)=&ProofGraph::allowRuleInterpolation;
  bool dupl_allowed_swap = true;
  bool dupl_allowed_cut = true;

  do
  {
    //Choose random clause and apply rule
    clause_num = rand() % graph.size();
    assert(clause_num < graph.size());
    n=graph[clause_num];

    if(n!=NULL && n->getAnt1()!=NULL && n->getAnt2()!=NULL)
    {
      //Look for rules applicability
      getApplContext(n->getAnt1()->getId(),n->getId(),ra1);
      getApplContext(n->getAnt2()->getId(),n->getId(),ra2);

      short chosen = handleRuleApplication(ra1,ra2,swap_rules_application_criterion,cut_rules_application_criterion,
	  dupl_allowed_swap,dupl_allowed_cut);

      if( chosen!=0 )
      {
	if(chosen==1)
	{
	  //cout << ra1.type << " ";
	  ruleApply(ra1);
	  rule_applied=true;
	  if(isCutRule(ra1.type) || ra1.type == rB2k)
	    //Do proof reconstruction
	    doTransformationLoop(done,&ProofGraph::trivialApplicationCriterion,&ProofGraph::trivialApplicationCriterion,true,true,false,false);
	}
	else if(chosen==2)
	{
	  //cout << ra2.type << " ";
	  ruleApply(ra2);
	  rule_applied=true;
	  if(isCutRule(ra2.type) || ra2.type == rB2k)
	    //Do proof reconstruction
	    doTransformationLoop(done,&ProofGraph::trivialApplicationCriterion,&ProofGraph::trivialApplicationCriterion,true,true,false,false);
	}
      }
    }
  }
  while(!rule_applied);

  //checkProof();
}

#endif
