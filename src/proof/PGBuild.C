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

void
ProofNode::setInterpPartitionMask()
{
    if(i_data == NULL) initIData();
    i_data->partition_mask = logic.getClauseClassMask(clause_ref);
    assert(i_data->partition_mask != 0);
#ifdef ITP_DEBUG
    cerr << "In Set, Clause " << clause_ref << " has mask " << i_data->partition_mask << endl;
#endif
}

void
ProofNode::setInterpPartitionMask( const ipartitions_t& mask)
{
    if(i_data == NULL) initIData();
    i_data->partition_mask = mask;
}

ostream& operator<< (ostream &out, RuleContext &ra)
{
	out << "Context: v1(" << ra.getV1() << ") v2(" << ra.getV2() << ") w("
			<< ra.getW() << ") v3(" << ra.getV3() << ") v("
			<< ra.getV() << ")";
	return out;
}


// Resolution proof builder
void ProofGraph::buildProofGraph( int nVars )
{
    if ( verbose() ) { cerr << "# " << "Proof graph building begin" << endl; }
    if ( verbose() > 0 )
    {
        uint64_t mem_used = memUsed();
        reportf( "# Memory used before building the proof: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
    }

    const double initTime=cpuTime();
    // Nominal number of variables
    assert( nVars>0 );
    num_vars_limit=nVars;
    max_id_variable=0;
#ifdef FULL_LABELING
    // Mapping for AB class variables
    AB_vars_mapping.reserve(num_vars_limit);
    AB_vars_mapping.resize(num_vars_limit,-3);
#endif

    av_cla_size=0; max_cla_size=0;
    num_edges=0;
    num_nodes=0;
    num_leaves=0;
    building_time=0;

    A1=0;
    A1prime=0;
    A1B=0;
    A2=0;
    A2B=0;
    A2U=0;
    B1=0;
    B2prime=0;
    B2=0;
    B3=0;
    duplications=0;
    swap_ties=0;

    // Resolution tree for clause id; pairs <clause,pivot>
    // Structure:
    // a -
    // b c
    // ...
    // a,b resolved over c...
    auto & clause_to_proof_der = proof.getProof( );
    map< CRef, ProofDer * >::iterator it;

    //To map clauses to graph id
    //An id is associated when the node is created
    map< CRef, int >* clauseToIDMap_ = new map< CRef, int>;
    map< CRef, int >& clauseToIDMap = *clauseToIDMap_;
    //To keep track of visited nodes
    set< CRef >* visitedSet_ = new set<CRef>;
    set< CRef >& visitedSet = *visitedSet_;
    //Queue to build proof graph from sink
    std::deque< CRef > q;

    unsigned      num_theory = 0;
    unsigned      num_clause = 0;
    unsigned      num_leaf = 0;
    unsigned      num_derived = 0;
    unsigned      num_learnt = 0;
    unsigned      max_leaf_size = 0;
    double        avg_leaf_size = 0;
    unsigned      max_learnt_size = 0;
    double        avg_learnt_size = 0;

    // NOTE: Must guarantee first antecedent -> positive occurrence pivot
    // second antecedent -> negative occurrence pivot

    // Map to associate node to its antecedents
    map< pair<int,int>, int >* ants_map_ = NULL;
    if ( enabledStructuralHashingWhileBuilding() )
    {
        ants_map_ = new map< pair<int,int>, int >;
    }
    map< pair<int,int>, int >& ants_map = *ants_map_;

    if ( verbose() && enabledStructuralHashingWhileBuilding() )
    { cerr << "; " << "Performing structural hashing while building the proof" << endl; }
    //Start from empty clause
    q.push_back(CRef_Undef);
    do
    {
        // Get current clause
        CRef currClause=q.back();
        q.pop_back();
        // Clause not visited yet
        if (visitedSet.find(currClause) == visitedSet.end())
        {
            // in case of (assert false), clause_to_proof_der[currClause] is actually NULL
            assert(clause_to_proof_der.find(currClause) != clause_to_proof_der.end());
            if (currClause == CRef_Undef && clause_to_proof_der.at(currClause).chain_cla.empty())
            {
                assert(graph.size() == 0);
                ProofNode* n = new ProofNode(logic_);
                n->initIData();
                // Add node to graph vector
                int currId = (int)graph.size();
                n->setId(currId);
                n->setType(clause_type::CLA_ORIG);
                vector<Lit> false_clause;
                Lit lit_false = PTRefToLit(logic_.getTerm_false());
                false_clause.push_back(lit_false);
                n->initClause(false_clause);
                // We should set the partition_mask here, but how is that
                // done?
//                ipartitions_t mask = 0x10; // This is arbitrary, we should somehow know in which partition the false is so we could get this right.
//                n->setInterpPartitionMask(mask);
                graph.push_back(n);
                assert(getNode(currId)==n);
                root=currId;
                if( verbose() > 0 )
                    reportf( "# (1) Empty clause given in input or generated at preprocessing time: single node proof\n" );
                break;
            }

            // Get clause derivation tree
            assert(clause_to_proof_der.find(currClause) != clause_to_proof_der.end());
            ProofDer &           proofder = clause_to_proof_der.at(currClause); // Derivation
            const vector< CRef > &     chaincla = proofder.chain_cla;            // Clauses chain
            const vector< Var > &      chainvar = proofder.chain_var;            // Pivot chain
            clause_type        ctype    = proofder.type;

            // No derivation tree: original clause
            // Non empty clause
            // Only boolean reasoning allowed
            if ( ctype == clause_type::CLA_ORIG || ctype == clause_type::CLA_THEORY )
            {
                if (ctype == clause_type::CLA_THEORY)
                {
                    if (chaincla.size() >= 2)
                    {
                        proofder.type = clause_type::CLA_LEARNT; // MB: TODO why reassigning type?
                        q.push_back(currClause);
                        continue;
                    }
                }
                if (ctype == clause_type::CLA_ORIG)
                    assert(chaincla.size()==0);
                // Empty clause (represented by NULL) has been labeled as original
                // if generated at preprocessing time
                if(ctype == clause_type::CLA_ORIG && currClause==CRef_Undef)
                {
                    assert(graph.size()==0);
                    ProofNode* n=new ProofNode(logic_);
                    n->initIData();
                    //n->initClause(proof.getClause(currClause));
                    // Add node to graph vector
                    int currId=(int)graph.size();
                    n->setId(currId);
                    n->setType(clause_type::CLA_ORIG);
                    graph.push_back(n);
                    assert(getNode(currId)==n);
                    root=currId;
                    if ( verbose() > 0 ) reportf( "# (2) Empty clause given in input or generated at preprocessing time: single node proof\n" );
                    break;
                }

                // Clause not processed yet
                if (clauseToIDMap.find(currClause)==clauseToIDMap.end())
                {
                    ProofNode* n = new ProofNode(logic_);
                    if (ctype == clause_type::CLA_ORIG) num_leaf++;
                    else num_theory++;
                    n->initClause(proof.getClause(currClause));
                    if(ctype == clause_type::CLA_ORIG)
                        n->setClauseRef(currClause);
                    // Add node to graph vector
                    int currId=(int)graph.size();
                    n->setId(currId);
                    graph.push_back(n);
                    assert(getNode(currId) == n);
                    //Update map clause->id
                    clauseToIDMap[currClause] = currId;
                    //Sort clause literals
                    std::sort(n->getClause().begin(),n->getClause().end());
                    if (ctype == clause_type::CLA_ORIG)
                    {
                        if ( n->getClauseSize() >= max_leaf_size ) max_leaf_size = n->getClauseSize();
                            avg_leaf_size += n->getClauseSize();
                    }
                }
                // NB: internal derived clauses not considered here
                //Original clause
                if (ctype == clause_type::CLA_ORIG)
                    getNode(clauseToIDMap[currClause])->setType(clause_type::CLA_ORIG);
                else
                    getNode(clauseToIDMap[currClause])->setType(clause_type::CLA_THEORY);
                //Determine partition mask in case of interpolation
                //if( produceInterpolants() > 0 )
                //      getNode(clauseToIDMap[currClause])->setInterpPartitionMask();
                addLeaf(clauseToIDMap[currClause]);
            }
            // Learnt clause
            // Resolution tree present
            else if(ctype==clause_type::CLA_LEARNT)
            {
                int last_seen_id = -1;
                assert(chaincla.size() >= 2);
                assert(chainvar.size() == chaincla.size()-1);

                // First clause not yet processed
                CRef clause_0 = chaincla[0];
                while(clause_to_proof_der.at(clause_0).chain_cla.size() == 1)
                    clause_0 = clause_to_proof_der.at(clause_0).chain_cla[0];

                if(clauseToIDMap.find(clause_0)==clauseToIDMap.end())
                {
                    ProofNode* n=new ProofNode(logic_);
                    n->initIData();
                    clause_type  _ctype    = clause_to_proof_der.at(clause_0).type;
                    if( _ctype==clause_type::CLA_ORIG )
                    {
                        n->initClause(proof.getClause(clause_0));
                        n->setClauseRef(clause_0);
                        //Sort clause literals
                        std::sort(n->getClause().begin(),n->getClause().end());
                        num_leaf++;
                        if( n->getClauseSize() >= max_leaf_size ) max_leaf_size = n->getClauseSize();
                        avg_leaf_size += n->getClauseSize();
                    }
                    else if (_ctype==clause_type::CLA_LEARNT )
                    {
                        num_learnt++;
                        //n->setClauseRef(clause_0);
                        unsigned ssize = proof.getClause(clause_0).size();
                        if( ssize >= max_learnt_size ) max_learnt_size = ssize;
                        avg_learnt_size += ssize;
                    }
                    else if(_ctype == clause_type::CLA_THEORY)
                    {
                        n->initClause(proof.getClause(clause_0));
                        n->setClauseRef(clause_0, false);
                        //Sort clause literals
                        std::sort(n->getClause().begin(),n->getClause().end());
                        ++num_theory;
                    }

                    //Add node to graph vector
                    int currId=(int)graph.size();
                    n->setId(currId);
                    graph.push_back(n);
                    assert(getNode(currId)==n);
                    //Update map clause->id
                    clauseToIDMap[clause_0]=currId;
                    //Add clause to queue
                    q.push_back(clause_0);
                    last_seen_id=currId;
                }
                else last_seen_id = clauseToIDMap[clause_0];

                // Check for internally deduced clauses
                for ( size_t i = 1 ; i < chaincla.size() ; i ++ )
                {
                    // ith clause not yet processed
                    CRef clause_i = chaincla[i];
                    while(clause_to_proof_der.at(clause_i).chain_cla.size() == 1)
                        clause_i = clause_to_proof_der.at(clause_i).chain_cla[0];


                    if(clauseToIDMap.find(clause_i)==clauseToIDMap.end())
                    {
                        ProofNode* n=new ProofNode(logic_);
                        n->initIData();
                        // Contains negative occurrence pivot
                        clause_type _ctype = clause_to_proof_der.at(clause_i).type;
                        if( _ctype==clause_type::CLA_ORIG )
                        {
                            n->initClause(proof.getClause(clause_i));
                            n->setClauseRef(clause_i);
                            //Sort clause literals
                            std::sort(n->getClause().begin(),n->getClause().end());
                            num_leaf++;
                            if( n->getClauseSize() >= max_leaf_size ) max_leaf_size = n->getClauseSize();
                            avg_leaf_size += n->getClauseSize();
                        }
                        else if (_ctype==clause_type::CLA_LEARNT )
                        {
                            num_learnt++;
                            unsigned ssize = proof.getClause(clause_i).size();
                            if( ssize >= max_learnt_size ) max_learnt_size = ssize;
                            avg_learnt_size += ssize;
                        }
                        else if(_ctype == clause_type::CLA_THEORY)
                        {
                            n->initClause(proof.getClause(clause_i));
                            n->setClauseRef(clause_i, false);
                            //Sort clause literals
                            std::sort(n->getClause().begin(),n->getClause().end());
                            ++num_theory;
                        }

                        //Add node to graph vector
                        int currId=(int)graph.size();
                        n->setId(currId);
                        graph.push_back(n);
                        assert(getNode(currId)==n);
                        //Update map clause->id
                        clauseToIDMap[clause_i]=currId;
                        //Add clause to queue
                        q.push_back(clause_i);
                    }
                    ProofNode* n = NULL;
                    int currId = -1;

                    // End tree not reached: deduced node
                    if(i<chaincla.size()-1)
                    {
                        currId=(int)graph.size();

                        ///////////////////////////////////////////////////////////////////////////////////////
                        // NOTE structural hashing: check whether there already
                        // exists a node with the current pair of antecedents
                        // if so, stop creating the proof chain
                        if( enabledStructuralHashingWhileBuilding() )
                        {
                            int id__i=clauseToIDMap[ clause_i ];
                            int c1, c2;
                            if(id__i <= last_seen_id)
                            { c1 = id__i; c2 =last_seen_id; }
                            else
                            { c2 = last_seen_id; c1 = id__i; }
                            // Look for pair <ant1,ant2>
                            pair<int, int> ant_pair (c1,c2);
                            map< pair<int,int>, int >::iterator it = ants_map.find( ant_pair );
                            bool found = ( it != ants_map.end() );
                            // If pairs not found, add id of the next node to the map
                            if( !found ) ants_map[ ant_pair ] = currId ;
                            // else replace node with existing one
                            else
                            {
                                ProofNode* replacing = getNode( it->second );
                                assert( replacing );
                                last_seen_id = it->second;
                                // Skip the new node construction and move to the next clause in the chain
                                continue;
                            }
                        }
                        //
                        //////////////////////////////////////////////////////////////////////////////////////////

                        n=new ProofNode(logic_); num_derived++;
                        n->initIData();
                        //Add node to graph vector
                        n->setId(currId);
                        graph.push_back(n);
                        assert(getNode(currId)==n);
                        n->setType(clause_type::CLA_DERIVED); // MB: TODO: investigate difference beteween learnt and derived
                    }
                    // End tree reached: currClause
                    else
                    {
                        if(clauseToIDMap.find(currClause)==clauseToIDMap.end())
                        {
                            currId=(int)graph.size();

                            ///////////////////////////////////////////////////////////////////////////////////////
                            // NOTE structural hashing: check whether there already
                            // exists a node with the current pair of antecedents
                            // if so, stop creating the proof chain
                            // Make sure ant1 has the pivot positive (and ant2 negated)

                            // NOTE: the technique does not seem to have effect here
                            if( enabledStructuralHashingWhileBuilding() )
                            {
                                int id__i=clauseToIDMap[ clause_i ];
                                int c1, c2;
                                if(id__i <= last_seen_id)
                                { c1 = id__i; c2 =last_seen_id; }
                                else
                                { c2 = last_seen_id; c1 = id__i; }
                                // Look for pair <ant1,ant2>
                                pair<int, int> ant_pair (c1,c2);
                                map< pair<int,int>, int >::iterator it = ants_map.find( ant_pair );
                                bool found = ( it != ants_map.end() );
                                // If pairs not found, add id of the next node to the map
                                if( !found ) ants_map[ ant_pair ] = currId ;
                                // else replace node with existing one
                                else
                                {
                                    ProofNode* replacing = getNode( it->second );
                                    assert( replacing );
                                    last_seen_id = it->second;
                                    // Skip the new node construction and move to the next clause in the chain
                                    continue;
                                }
                            }
                            //
                            //////////////////////////////////////////////////////////////////////////////////////////

                            n=new ProofNode(logic_); num_learnt++;
                            unsigned ssize = ( currClause == CRef_Undef ) ? 0 : proof.getClause(currClause).size();
                            if( ssize >= max_learnt_size ) max_learnt_size = ssize;
                            avg_learnt_size += ssize;
                            n->initIData();
                            //Add node to graph vector
                            n->setId(currId);
                            graph.push_back(n);
                            assert(getNode(currId)==n);
                            //Update map clause->id
                            clauseToIDMap[currClause]=currId;
                        }
                        currId = clauseToIDMap[currClause];
                        n = getNode(currId);
                        n->setType(clause_type::CLA_LEARNT);

                        //Sink check
                        if(currClause==CRef_Undef) root=currId;
                    }
                    assert(n);
                    // Edges creation
                    // First internal node deduced from first clauses 0 and 1
                    // Other internal nodes deduced from last internal node and clause i
                    n->setPivot(chainvar[i-1]); proof_variables.insert(chainvar[i-1]);
                    if(chainvar[i-1] > max_id_variable) max_id_variable = chainvar[i-1];
                    assert(last_seen_id>=0); assert(currId>=0);

                    bool pos_piv = true;
                    bool found_piv = false;
                    // Make sure ant1 has the pivot positive (and ant2 negated)
                    Clause& clausei = proof.getClause(clause_i);
                    for(int k=0;k<clausei.size();k++)
                    {
                        if( var( clausei[k] ) == n->getPivot() )
                        {
                            if(sign( clausei[k] ) != 0) { pos_piv=false; }
                            found_piv = true;
                            break;
                        }
                    }
                    assert( found_piv );
                    int id_i=clauseToIDMap[clause_i];
                    if(pos_piv)
                    {
                        n->setAnt1(getNode(id_i));
                        n->setAnt2(getNode(last_seen_id));
                    }
                    else
                    {
                        n->setAnt1(getNode(last_seen_id));
                        n->setAnt2(getNode(id_i));
                    }
                    last_seen_id = currId;
                    n->getAnt1()->addRes( n->getId() );
                    n->getAnt2()->addRes( n->getId() );
                }
            }
            //Mark clause as visited
            visitedSet.insert(currClause);
            num_clause++;
        }
    }
    while(!q.empty());
    delete clauseToIDMap_;
    delete visitedSet_;
    if ( enabledStructuralHashingWhileBuilding() ) delete(ants_map_);

    if( proofCheck() )
    {
        // Check whether there are any remaining pieces
        checkProof( false );
        unsigned rem = cleanProofGraph( );
        assert( rem == 0 );
    }

    if( verbose() > 0 )
    {
        unsigned num_non_null=0;
        unsigned cl_non_null=0;
        for(size_t i=0;i<getGraphSize();i++)
        {
            if(getNode(i)!=NULL) num_non_null++;
            if(getNode(i)->getPClause() != NULL) cl_non_null++;
        }
#ifdef PEDANTIC_DEBUG
        cout << "Graph size: " << getGraphSize() << endl;
        cout << "Non null nodes: " << num_non_null << endl;
        cout << "Non null clauses: " << cl_non_null << endl;
#endif
        if(graph.size() > 1)
            assert( num_non_null == (num_leaf + num_learnt + num_derived + num_theory) );

        reportf( "# Number of nodes: %d (leaves: %d - learnt: %d - derived: %d - theory: %d)\n", num_non_null, num_leaf, num_learnt, num_derived, num_theory );
        reportf( "# Maximum, average size of leaves: %d  %.2f\n", max_leaf_size, avg_leaf_size/(double)num_leaf );
        reportf( "# Maximum, average size of learnt: %d  %.2f\n", max_learnt_size, avg_learnt_size/(double)num_learnt );
        reportf( "# Number of edges: %d\n", (num_learnt + num_derived)*2 );
        num_nodes = num_non_null;
        num_edges = (num_learnt + num_derived)*2;
        //reportf( "# Number of variables - nominal: %d - actual: %d\n",  num_vars_limit, proof_variables.size() );
        reportf( "# Number of distinct variables in the proof: %d\n", (int)proof_variables.size() );
    }
    if ( verbose() > 0 )
    {
        uint64_t mem_used = memUsed();
        reportf( "# Memory used after building the proof: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
    }
    if ( verbose() ) { cerr << "# " << "Proof graph building end" << endl; }
    building_time=cpuTime()-initTime;

    if( proofCheck() )
    {
        verifyLeavesInconsistency();
    }
}

void ProofGraph::fillProofGraph()
{
	if ( verbose() > 1 )
	{
		uint64_t mem_used = memUsed();
		reportf( "# Memory used before filling the proof: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}

	vector<clauseid_t>q;
	clauseid_t id;
	ProofNode* n=NULL;
	q.push_back(getRoot()->getId());
	do
	{
		id=q.back();
		n=getNode(id);
		//Node not visited yet
		if(!isSetVisited1(id))
		{
			// Enqueue antecedents if not visited
			if(n->getAnt1()!=NULL && !isSetVisited1(n->getAnt1()->getId()))
				q.push_back(n->getAnt1()->getId());
			else if(n->getAnt2()!=NULL && !isSetVisited1(n->getAnt2()->getId()))
				q.push_back(n->getAnt2()->getId());
			// Mark node as visited if both antecedents visited
			else
			{
				setVisited1(id);
				q.pop_back();
				assert(n);
				//Non leaf node
				if(!n->isLeaf())
				{
					n->initClause();
					mergeClauses(n->getAnt1()->getClause(), n->getAnt2()->getClause(), n->getClause(), n->getPivot());
				}
			}
		}
		else q.pop_back();
	}
	while(!q.empty());
	resetVisited1();

	if ( verbose() > 0 )
	{
		uint64_t mem_used = memUsed();
		reportf( "# Memory used after filling the proof: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}
}

void ProofGraph::emptyProofGraph()
{
	if ( verbose() > 1 )
	{
		uint64_t mem_used = memUsed();
		reportf( "# Memory used before emptying the proof: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}
	ProofNode* n = NULL;
	for(size_t i=0;i< getGraphSize() ;i++)
	{
		n=getNode(i);
		if( n!=NULL && !n->isLeaf() ) { n->resetClause(); }
	}
	if ( verbose() > 0 )
	{
		uint64_t mem_used = memUsed();
		reportf( "# Memory used after emptying the proof: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}
}

void ProofGraph::normalizeAntecedentOrder()
{
	// Normalize proof for interpolation
	std::deque<ProofNode*> q;
	ProofNode* n;
	q.push_back(getRoot());
	do
	{
		n=q.front();
		q.pop_front();
		if(!isSetVisited1(n->getId()))
		{
			if(!n->isLeaf())
			{
				q.push_back(n->getAnt1());
				q.push_back(n->getAnt2());

				// Check pivot in antecedents
				short f1 = n->getAnt1()->hasOccurrenceBin(n->getPivot());
				short f2 = n->getAnt2()->hasOccurrenceBin(n->getPivot());
				assert( f1!=-1 && f2!=-1 );
				assert( !(f1==1 && f2==1) && !(f1==0 && f2==0) );
				// Exchange antecedents if necessary
				if( f1==1 && f2==0 )
				{
					ProofNode* aux = n->getAnt1();
					n->setAnt1( n->getAnt2() );
					n->setAnt2( aux );
				}
			}
			setVisited1(n->getId());
		}
	}
	while(!q.empty());
	resetVisited1();
}

int ProofGraph::cleanProofGraph()
{
	// Remove the unreachable part of the graph
	// Ideally it will be made of subgraphs not connected to the main graph
	unsigned removed=0;
	bool done = false;
	unsigned counter = 0;
	while(!done)
	{
		done = true;
		counter ++;
		for(size_t i=0;i< getGraphSize() ;i++)
		{
			if(getNode(i)!=NULL && getNode(i)->getNumResolvents()==0 && getNode(i)!=getRoot())
			{
				done = false;
				removed += removeTree(i);
				//cerr << "Detached tree starting at " << i << endl;
			}
		}
	}
	return removed;
}

//Remove a node from the graph
void ProofGraph::removeNode(clauseid_t vid)
{
	ProofNode* n=getNode(vid);
	assert(n);
	if(n->getAnt1()==NULL && n->getAnt2()==NULL) removeLeaf(vid);
	n->setAnt1(NULL); n->setAnt2(NULL);
	// Free memory
	n->delIData();
	delete n;
	// Remove v from proof
	graph[vid]=NULL;
}

unsigned ProofGraph::removeTree( clauseid_t vid )
{
	assert(getNode(vid));
	assert(getNode(vid)->getNumResolvents() == 0 );
	unsigned removed=0;

	//Go on removing nodes with 0 resolvents
	//Visit graph from root keeping track of edges and nodes
	std::deque< clauseid_t > q;
	ProofNode * n;
	clauseid_t c;
	// Better a set than a boolean vector to avoid wasting memory
	std::set<clauseid_t> visit;


	/*
 	// For some reason this code leaves some hanging nodes with RecyclePivots
 	q.push_back( vid );
	do
	{
		c = q.front( );
		q.pop_front( );
		assert( c < getGraphSize() );

		//Node not visited yet
		if(visit.find(c) == visit.end())
		{
			n = getNode(c);
			assert( n );
			//Mark node as visited
			visit.insert(c);
			//Remove node if no more resolvents present
			if( n->getNumResolvents() == 0 )
			{
				if( n->getAnt1()!=NULL )
				{
					assert(getNode(n->getAnt1()->getId())==n->getAnt1());
					q.push_back( n->getAnt1()->getId() );
					n->getAnt1()->remRes( c );
				}
				if( n->getAnt2()!=NULL )
				{
					assert(getNode(n->getAnt2()->getId())==n->getAnt2());
					q.push_back( n->getAnt2()->getId() );
					n->getAnt2()->remRes( c );
				}
				removeNode( c );
				removed++;
			}
		}
	}
	while( !q.empty( ) );*/

	q.push_back( vid );
	do
	{
		c = q.front( );
		q.pop_front( );
		assert( c < getGraphSize() );
		n = getNode(c);
		//Remove node if no more resolvents present
		if( n!= NULL && n->getNumResolvents() == 0 )
		{
			if( n->getAnt1()!=NULL )
			{
				assert(getNode(n->getAnt1()->getId())==n->getAnt1());
				q.push_back( n->getAnt1()->getId() );
				n->getAnt1()->remRes( c );
			}
			if( n->getAnt2()!=NULL )
			{
				assert(getNode(n->getAnt2()->getId())==n->getAnt2());
				q.push_back( n->getAnt2()->getId() );
				n->getAnt2()->remRes( c );
			}
			removeNode( c );
			removed++;
		}
	}
	while( !q.empty( ) );

	return removed;
}

clauseid_t ProofGraph::dupliNode( RuleContext& ra )
{
	//cerr << "Duplicating " << ra.getW() << " in rule " << ra.getType() << endl;
	clauseid_t v_id = ra.getV();
	ProofNode* w = getNode( ra.getW() );
	assert(w);
	unsigned num_old_res = w->getNumResolvents();
	assert( num_old_res > 1);
	for( set<clauseid_t>::iterator it = w->getResolvents().begin(); it!=w->getResolvents().end(); it++)
	{
		ProofNode* res = getNode( (*it) ); assert(res);
		assert(res->getAnt1()==w || res->getAnt2()==w);
	}

	ProofNode* n=new ProofNode(logic_);
	n->initIData();

	// Create node and add to graph vector
	clauseid_t currId=getGraphSize();
	n->setId(currId);
	graph.push_back(n);
	assert(getNode(currId)==n);
	n->setType(w->getType());
	n->initClause(w->getClause());
    n->setInterpPartitionMask(w->getInterpPartitionMask());

	// Set antecedents, pivot
	n->setAnt1(w->getAnt1());
	n->setAnt2(w->getAnt2());
	n->getAnt1()->addRes(currId);
	n->getAnt2()->addRes(currId);
	n->setPivot(w->getPivot());

	// The new node replaces w in the context
	// w loses v but keeps everything else
	ProofNode* v = getNode(v_id);
	w->remRes(v_id);
	n->addRes(v_id);
	if(v->getAnt1() == w) v->setAnt1(n);
	else if(v->getAnt2() == w) v->setAnt2(n);
	else opensmt_error_();
	assert( w->getResolvents().find(v_id) == w->getResolvents().end());
	assert( w->getNumResolvents() == num_old_res - 1);
	// Remember to modify context
	ra.cw = currId;

	duplications++;
	return currId;
}

#endif
