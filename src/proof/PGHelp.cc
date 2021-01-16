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
#include <math.h>

short ProofNode::hasOccurrenceBin(Var v) {
    vector< Lit >& cla = getClause();
    int first=0;
    int last=cla.size()-1;

    while (first <= last) {
        int mid = (first + last) / 2;
        Lit l = cla[mid]; Var w = var(l);
        if (v > w) first = mid + 1;
        else if (v < w) last = mid - 1;
        else if( v == w ) return (sign(l) == false) ? 0 : 1;
    }
    return -1;
}

// Calculate graph info
// Assume proof filled
void ProofGraph::getGraphInfo()
{
    //Visit graph from sink keeping track of edges and nodes
    std::deque<ProofNode*> q;
    ProofNode* n;

    av_cla_size=0;
    max_cla_size=0;
    var_cla_size=0;
    num_nodes=0;
    num_edges=0;
    num_unary=0;
    num_leaves=0;
    proof_variables.empty();

    q.push_back(getRoot());
    do
    {
        n=q.front();
        q.pop_front();

        // Node not visited yet
        if (!isSetVisited1(n->getId()))
        {
            if (!n->isLeaf())
            {
                q.push_back(n->getAnt1());
                num_edges++;
                q.push_back(n->getAnt2());
                num_edges++;
                proof_variables.insert(n->getPivot());
            }
            else
            {
                assert(n->getType()==clause_type::CLA_ORIG || n->getType() == clause_type::CLA_THEORY);
                num_leaves++;
            }

            //Mark node as visited
            setVisited1(n->getId());
            num_nodes++;
            av_cla_size+=n->getClauseSize();
            if (n->getClauseSize() > (size_t)max_cla_size) max_cla_size=n->getClauseSize();
            if (n->getClauseSize()==1) num_unary++;
        }
    }
    while(!q.empty());

    av_cla_size /= num_nodes;
    // Calculate sample variance for num resolvents and clause size
    for (size_t i=0;i<getGraphSize();i++)
        if (getNode(i)!=NULL)
        {
            var_cla_size+=pow(getNode(i)->getClauseSize()-av_cla_size,2);
        }
    var_cla_size/=(num_nodes-1);
    resetVisited1();
    //Calculate sample variance for clause size

    /*  if(verbose())
    {
        cerr << "#" << endl;
        cerr << "# ------------------------------------" << endl;
        cerr << "# PROOF GRAPH STATISTICS    " << endl;
        cerr << "# ------------------------------------" << endl;
        cerr << "# Actual num proof variables.: "; fprintf( stderr, "%-10d\n", proof_variables.size() );
        cerr << "# Nodes......................: "; fprintf( stderr, "%-10d\n", num_nodes );
        cerr << "# Leaves.....................: "; fprintf( stderr, "%-10d\n", num_leaves );
        cerr << "# Edges......................: "; fprintf( stderr, "%-10d\n", num_edges );
        cerr << "# Graph vector size..........: "; fprintf( stderr, "%-10ld\n", graph.size( ) );
        cerr << "# Average degree.............: "; fprintf( stderr, "%-10.2f\n", (double)num_edges / (double)num_nodes );
        cerr << "# Unary clauses..............: "; fprintf( stderr, "%-10d\n", num_unary );
        cerr << "# Max clause size............: "; fprintf( stderr, "%-10d\n", max_cla_size );
        cerr << "# Average clause size........: "; fprintf( stderr, "%-10.2f\n", av_cla_size );
        cerr << "# Variance clause size.......: "; fprintf( stderr, "%-10.2f\n", var_cla_size );
        cerr << "# ---------------------------" << endl;
    }*/
}

//Input: a vector which will contain the topological sorting of nodes
//Output: a topological sorting antecedents-resolvents
void ProofGraph::topolSortingTopDown(vector<clauseid_t>& DFS)
{
    std::deque<clauseid_t>q;
    ProofNode* n;
    DFS.clear();
    DFS.reserve(getGraphSize());
    if (getGraphSize() == 1)
    {
        DFS.push_back(graph[0]->getId());
        return;
    }
    clauseid_t id;
    // Enqueue leaves first
    q.assign(leaves_ids.begin(),leaves_ids.end());
    do
    {
        id=q.front(); q.pop_front();
        n=getNode(id); assert(n);
        //Node not visited yet
        if (!isSetVisited1(id))
        {
            if (n->getAnt1()!=NULL && !isSetVisited1(n->getAnt1()->getId())){}
            else if (n->getAnt2()!=NULL && !isSetVisited1(n->getAnt2()->getId())){}
            // Mark node as visited if both antecedents visited
            else
            {
                // Enqueue resolvents
                for (set<clauseid_t>::iterator it = n->getResolvents().begin(); it != n->getResolvents().end(); it++ )
                    if (getNode(*it) != NULL) q.push_back(*it);
                setVisited1(id);
                DFS.push_back(id);
            }
        }
    }
    while(!q.empty());
    resetVisited1();
}

//Input: a vector which will contain the topological sorting of nodes
//Output: a topological sorting antecedents-resolvents
void ProofGraph::topolSortingBotUp(vector<clauseid_t>& DFS)
{
    clauseid_t id,id1,id2;
    vector<clauseid_t> q;
    ProofNode * node = NULL;
    std::vector<unsigned>* visited_count_ = new vector<unsigned>(getGraphSize(),0);
    std::vector<unsigned>& visited_count = *visited_count_;
    DFS.clear();
    DFS.reserve(getGraphSize());

    // Building DFS vector
    q.push_back(getRoot()->getId());
    do
    {
        id = q.back();
        node = getNode(id);
        assert(node);
        visited_count[id]++;
        q.pop_back();

        // All resolvents have been visited
        if (id == getRoot()->getId() || visited_count[id] == node->getNumResolvents())
        {
            if (!node->isLeaf())
            {
                id1 = node->getAnt1()->getId();
                id2 = node->getAnt2()->getId();
                // Enqueue antecedents
                assert( visited_count[id1] < node->getAnt1()->getNumResolvents() );
                assert( visited_count[id2] < node->getAnt2()->getNumResolvents() );
                q.push_back(id1); q.push_back(id2);
            }
            DFS.push_back(id);
        }
    }
    while(!q.empty());
    delete visited_count_;
}

// Linear merge for resolution
bool ProofGraph::mergeClauses(vector<Lit>& A, vector<Lit>& B, vector<Lit>& resolv, Var pivot)
{
    size_t i, j;
    i = 0;
    j = 0;
    const size_t Asize= A.size();
    const size_t Bsize= B.size();
    size_t ressize=0;
    if(resolv.size() < Asize + Bsize - 2)
    {
        resolv.reserve(Asize + Bsize - 2);
        resolv.resize(Asize + Bsize - 2);
    }
    assert(resolv.size() >= Asize + Bsize - 2);

    //Insert first element
    if(var(A[i])==pivot) i++;
    if(var(B[j])==pivot) j++;
    if(i < Asize && j < Bsize) {
        if (A[i]<=B[j]) {
            if(var(A[i])!=pivot){ resolv[ressize]=A[i]; ressize++; }
            i++;
        }
        else {
            if(var(B[j])!=pivot){ resolv[ressize]=B[j]; ressize++; }
            j++;
        }
    }
    else if (i < Asize) {
        if(var(A[i])!=pivot){ resolv[ressize]=A[i]; ressize++; }
        i++;
    }
    else if (j< Bsize) {
        if(var(B[j])!=pivot){ resolv[ressize]=B[j]; ressize++; }
        j++;
    }

    //Insert further elements avoiding repetitions
    while (i < Asize && j < Bsize) {
        if (A[i]<=B[j]) {
            if(var(A[i])!=pivot && A[i] != resolv[ressize-1]){ resolv[ressize]=A[i]; ressize++; }
            i++;
        } else {
            if(var(B[j])!=pivot && B[j] != resolv[ressize-1]){ resolv[ressize]=B[j]; ressize++; }
            j++;
        }
    }
    if (i < Asize)
    {
        for (size_t p = i; p < Asize; p++)
            if(var(A[p])!=pivot && A[p]!=resolv[ressize-1]){ resolv[ressize]=A[p]; ressize++; }
    }
    else if(j < Bsize)
    {
        for (size_t p = j; p < Bsize; p++)
            if(var(B[p])!=pivot && B[p]!=resolv[ressize-1]){ resolv[ressize]=B[p]; ressize++; }
    }
    if( resolv.size() < ressize )
    {
        printClause( cerr, A ); cerr << endl;
        printClause( cerr, B ); cerr << endl;
    }
    assert( resolv.size() >= ressize );
    resolv.resize( ressize );
    return true;
}


/////////INTERPOLATION////////////

/************************ OTHER *********************************/

// Output: formula complexity as number of connectives, number of distinct boolean variables
void ProofGraph::getComplexityInterpolant( PTRef int_e )
{
    // Computation embedded in topological visit enode
    assert( int_e != PTRef_Undef );

    vector<PTRef>q;
    PTRef e_curr;
    set<PTRef>* visited_= new set<PTRef>;
    set<PTRef>& visited = *visited_;
    set<Var>* predicates_ = new set<Var>();
    set<Var>& predicates = *predicates_;
    map< PTRef, unsigned long >* complexity_map_ = new map< PTRef, unsigned long >();
    map< PTRef, unsigned long >& complexity_map = *complexity_map_;
    unsigned num_connectives_dag = 0;
    unsigned num_and_or_dag = 0;

    q.push_back(int_e);
    do
    {
        e_curr=q.back();
        assert(e_curr != PTRef_Undef );
        //Node not visited yet
        if (visited.find(e_curr) == visited.end())
        {
            bool all_visited = false;
            // Atomic boolean expression
            if (logic_.isAtom(e_curr))
            {
                // Complexity of atom is 0
                complexity_map.insert( std::make_pair( e_curr, 0 ) );
#ifdef PEDANTIC_DEBUG
                cerr << "; Adding complexity of " << logic.printTerm(e_curr) << " = 0" << endl;
#endif
                // Add predicate to set
                if ( e_curr != logic_.getTerm_true() && e_curr != logic_.getTerm_false() ) predicates.insert(PTRefToVar( e_curr ));
                visited.insert(e_curr);
                q.pop_back();
            }
            // Non atomic boolean expression
            else if ( logic_.isBooleanOperator(e_curr))
            {
                assert( logic_.isAnd(e_curr) || logic_.isOr(e_curr) || logic_.isNot(e_curr) || logic_.isEquality(e_curr) );
//                      assert( e_curr->getCar()->isSymb() );
//                      PTRef args = e_curr->getCdr();
//                      assert( args->isList( ) );
                all_visited = true;
                unsigned long comp_curr=0;
                unsigned long num_args=0;
                // Scan arguments of connective
//                      for ( PTRef alist = args ; !alist->isEnil( ) && all_visited; alist = alist->getCdr( ) )
#ifdef PEDANTIC_DEBUG
                cerr << "; Checking if all the children of " << logic.printTerm(e_curr) << " are visited" << endl;                
#endif
                Pterm& t = logic_.getPterm(e_curr);
                for (int i = 0; i < t.size(); i++)
                {
//                          PTRef sub_e = alist->getCar( );
                    PTRef sub_e = t[i];
                    assert( logic_.isBooleanOperator(sub_e) || logic_.isAtom(sub_e) );
                    if(visited.find(sub_e) == visited.end())
                    {
                        q.push_back(sub_e);
                        all_visited=false;
#ifdef PEDANATIC_DEBUG
                        cerr << "; Pushing " << logic.printTerm(sub_e) << endl;
#endif
                    }
                    else
                    {
                        // Calculate complexity
                        comp_curr += complexity_map.find(sub_e)->second;
#ifdef PEDANTIC_DEBUG
                        cerr << "; Child " << logic.printTerm(sub_e) << " already visited, complexity " << complexity_map.find(sub_e)->second << endl;
#endif
                        num_args++;
                    }
                }
                if(all_visited)
                {
#ifdef PEDANTIC_DEBUG
                    cerr << "; All children of " << logic.printTerm(e_curr) << " are visited" << endl;
#endif
                    unsigned additional_compl = 0;

                    // Formula tree representation
                    if( logic_.isAnd(e_curr) || logic_.isOr(e_curr) ) additional_compl = num_args - 1;
                    else if( logic_.isNot(e_curr) ) { assert(num_args==1); additional_compl = 1; }
                    complexity_map.insert(std::make_pair(e_curr, comp_curr + additional_compl));
#ifdef PEDANTIC_DEBUG
                    cerr << "; Complexity of " << logic.printTerm(e_curr) << " = " << complexity_map.find(e_curr)->second << endl;
#endif

                    // Formula dag representation
                    if( logic_.isAnd(e_curr) || logic_.isOr(e_curr) ) { additional_compl = num_args - 1; num_and_or_dag = num_and_or_dag + additional_compl; }
                    else if( logic_.isNot(e_curr) ) additional_compl = 1;
                    num_connectives_dag = num_connectives_dag + additional_compl;

                    visited.insert(e_curr);
                    q.pop_back();
                }
            }
            else opensmt_error_();
        }
        else
            q.pop_back();
    }
    while(!q.empty());
    unsigned long int_size = complexity_map.find(int_e)->second;
    unsigned pred_num = predicates.size();
    cerr << "# Interpolant number of connectives (dag  representation): " << num_connectives_dag << endl;
    cerr << "# Interpolant number of connectives (tree representation): " << int_size << endl;
    cerr << "# Interpolant number of distinct variables: " << pred_num << endl;
    delete( complexity_map_ );
    delete( predicates_ );
    delete( visited_ );
}


// Input: an interpolant, a boolean
// Output: complexity of interpolant (2 ways depending on the flag)
// Improved iterative implementation using topological visit of enode
unsigned long ProofGraph::getComplexityInterpolantIterative(PTRef int_e, bool flag)
{
	assert( int_e != PTRef_Undef );

	vector< PTRef > DFS_enode;
	topolSortingEnode( DFS_enode, int_e );

	map< PTRef, unsigned long > complexity_map;
	PTRef curr_enode;

	for( size_t i = 0; i < DFS_enode.size( ) ; i++ )
	{
		curr_enode= DFS_enode[i];
		assert(curr_enode != PTRef_Undef);

		// Case atom
		if( logic_.isAtom(curr_enode) )
		{
			// Complexity of atom is 0
			complexity_map.insert( std::make_pair( curr_enode, 0 ) );
		}
		// Case boolean connective: and, or not, iff, xor, implies
		else if( logic_.isBooleanOperator(curr_enode) )
		{
//			PTRef args = curr_enode->getCdr();
//			assert( args->isList( ) );

			unsigned long comp_curr=0;
			unsigned long num_args=0;
			// Scan arguments of connective
//			for ( PTRef alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
			Pterm& t = logic_.getPterm(curr_enode);
			for ( int i = 0; i < t.size(); i++ )
			{
				PTRef e = t[i];
				assert( logic_.hasSortBool(e) );
				// Calculate complexity
				comp_curr += complexity_map.find(e)->second;
				num_args++;
			}
			if( flag )
			{
				// Complexity of connective is sum of complexities of arguments plus one
				complexity_map.insert(std::make_pair(curr_enode,comp_curr + 1));
			}
			else
			{
				// Complexity of connective is sum of complexities of arguments plus number of arguments - 1
				// E.g. ennary AND counts as eight binary AND
				complexity_map.insert(std::make_pair(curr_enode,comp_curr + num_args -1));
			}
		}
	}
	return complexity_map.find(int_e)->second;
}

// Input: an interpolant
// Output: the set of predicates contained in the interpolant
// Better iterative version
void ProofGraph::getPredicatesSetFromInterpolantIterative(PTRef int_e, set< PTRef >& pred_set)
{
	assert( int_e != PTRef_Undef );

	vector< PTRef > DFS_enode;
	topolSortingEnode( DFS_enode, int_e );

	map< PTRef, set< PTRef > > predicate_map;
	set< PTRef >::iterator it;
	PTRef curr_enode;

	for( size_t i = 0 ; i < DFS_enode.size( ) ; i++ )
	{
		curr_enode = DFS_enode[i];
		assert( curr_enode != PTRef_Undef );

		set< PTRef > pred_set_curr;

		// Case atom
		if( logic_.isAtom(curr_enode) )
		{
			pred_set_curr.insert(curr_enode);
			predicate_map.insert(std::make_pair(curr_enode,pred_set_curr));
		}
		// Case boolean connective: and, or not, iff, xor, implies
		else if( logic_.isBooleanOperator(curr_enode) )
		{
//			PTRef args = curr_enode->getCdr();
//			assert( args->isList( ) );

			// Scan arguments of connective
//			for ( PTRef alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
			Pterm& t = logic_.getPterm(curr_enode);
			for ( int i = 0; i < t.size(); i++ )
			{
//				PTRef e = alist->getCar( );
				PTRef e = t[i];
				assert( logic_.hasSortBool(e) );
				// Add predicates
				set<PTRef> sub_pred_set = predicate_map.find(e)->second;
				for(it = sub_pred_set.begin(); it!=sub_pred_set.end(); it++ )
					pred_set_curr.insert((*it));
			}
			predicate_map.insert(std::make_pair(curr_enode,pred_set_curr));
		}
	}
	pred_set = predicate_map.find(int_e)->second;
}

// Input: an empty vector, an enode representing a boolean formula
// Output: a topological sorting of the enode subexpressions
void ProofGraph::topolSortingEnode(vector<PTRef>& DFS, PTRef int_e)
{
	assert( int_e != PTRef_Undef );
	assert( DFS.empty() );

	vector<PTRef>q;
	PTRef e_curr;
	DFS.clear();
	set<PTRef> visited;
	bool all_visited;

	q.push_back(int_e);
	do
	{
		e_curr=q.back();
		assert(e_curr != PTRef_Undef);
		//Node not visited yet
		if(visited.find(e_curr) == visited.end())
		{
			all_visited = false;
			// Atomic boolean expression
			if(logic_.isAtom(e_curr))
			{
				all_visited = true;
			}
			// Non atomic boolean expression
			else if( logic_.isBooleanOperator(e_curr) )
			{
//				PTRef args = e_curr->getCdr();
//				assert( args->isList( ) );

				all_visited = true;
				// Scan arguments of connective
//				for ( PTRef alist = args ; !alist->isEnil( ) ; alist = alist->getCdr( ) )
				Pterm& t = logic_.getPterm(e_curr);
				for ( int i = 0; i < t.size(); i++ )
				{
//					PTRef sub_e = alist->getCar( );
					PTRef sub_e = t[i];
					assert( logic_.hasSortBool(sub_e) );

					if(visited.find(sub_e) == visited.end())
					{
						q.push_back(sub_e);
						all_visited=false;
					}
				}
			}
			if(all_visited)
			{
				visited.insert(e_curr);
				q.pop_back();
				DFS.push_back(e_curr);
			}
		}
		else
			q.pop_back();
	}
	while(!q.empty());
}

void ProofGraph::analyzeProofLocality(const ipartitions_t & A_mask)
{
	cerr << "# Analyzing proof locality" << endl;
	unsigned num_A_local = 0, num_B_local = 0, num_AB_common = 0, num_AB_mixed = 0, num_sym_elim = 0;
	//Visit graph from sink keeping track of edges and nodes
	std::deque<ProofNode*> q;
	ProofNode* n;
	std::deque<bool> visit(getGraphSize(),false);

	q.push_back(getRoot());
	do
	{
		n=q.front();
		q.pop_front();

		//Node not visited yet
		if(!visit[n->getId()])
		{
			if(!n->isLeaf())
			{
				q.push_back(n->getAnt1());
				q.push_back(n->getAnt2());

				// Determine if resolution step is local, that is
				// 1) all variables are A or AB
				// 2) all variables are B or AB
				bool clause_has_A_local = false;
				bool clause_has_B_local = false;
				// Determine if resolution step is symbol-eliminating, that is
				// 1) At least an antecedent has local variables
				// 2) The resolvent has only AB variables
				bool resolvent_is_clean = false;
				std::vector<Lit>& c1 = n->getAnt1()->getClause();
				std::vector<Lit>& c2 = n->getAnt2()->getClause();
				std::vector<Lit>& c = n->getClause();

				for(unsigned i = 0; i < c1.size(); i++)
				{
					icolor_t v_class = getVarClass( var(c1[i]), A_mask );
					if( v_class == I_A ){ clause_has_A_local = true; }
					else if( v_class == I_B ){ clause_has_B_local = true; }
					else if( v_class == I_AB ){}
					else opensmt_error_();
				}
				for(unsigned i = 0; i < c2.size(); i++)
				{
					icolor_t v_class = getVarClass( var(c2[i]), A_mask );
					if( v_class == I_A ){ clause_has_A_local = true; }
					else if( v_class == I_B ){ clause_has_B_local = true; }
					else if( v_class == I_AB ){}
					else opensmt_error_();
				}
				for(unsigned i = 0; i < c.size(); i++)
				{
					icolor_t v_class = getVarClass( var(c[i]), A_mask );
					if( v_class == I_A ){ clause_has_A_local = true; resolvent_is_clean = false; }
					else if( v_class == I_B ){ clause_has_B_local = true; resolvent_is_clean = false; }
					else if( v_class == I_AB ){}
					else opensmt_error_();
				}
				if (!clause_has_A_local && !clause_has_B_local)     num_AB_common++;
				else if (clause_has_A_local && !clause_has_B_local) num_A_local++;
				else if (!clause_has_A_local && clause_has_B_local) num_B_local++;
				else if (clause_has_A_local && clause_has_B_local)  num_AB_mixed++;
				if((clause_has_A_local || clause_has_B_local) && resolvent_is_clean) num_sym_elim++;
			}
			else
			{
				// Determine if leaf is symbol-eliminating, that is
				// 1) The leaf has only AB variables
				bool clause_has_A_local = false;
				bool clause_has_B_local = false;
				std::vector<Lit>& c = n->getClause();

				for(unsigned i = 0; i < c.size(); i++)
				{
					icolor_t v_class = getVarClass( var(c[i]), A_mask );
					if( v_class == I_A ){ clause_has_A_local = true; }
					else if( v_class == I_B ){ clause_has_B_local = true; }
					else if( v_class == I_AB ){}
					else opensmt_error_();
				}
				if (!clause_has_A_local && !clause_has_B_local) num_sym_elim++;
			}
			//Mark node as visited
			visit[n->getId()]=true;
		}
	}
	while(!q.empty());
	cerr << "# AB common steps  :" << num_AB_common << endl;
	cerr << "# A local steps    :" << num_A_local << endl;
	cerr << "# B local steps    :" << num_B_local << endl;
	cerr << "# A B mixed steps  :" << num_AB_mixed << endl;
	cerr << "# Sym elim steps   :" << num_sym_elim << endl;
}
