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
#include "CoreSMTSolver.h" // TODO: MB: deal with reportf and remove this include

#include <unordered_set>

//************************* RECYCLE PIVOTS AND RECYCLE UNITS ***************************

double ProofGraph::recyclePivotsIter()
{
	if ( verbose() > 1 ) { std::cerr << "; Recycle pivots plus restructuring begin" << std::endl; }
	if ( verbose() > 1 )
	{
		uint64_t mem_used = memUsed();
		reportf( "; Memory used before recycling: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}
	double initTime=cpuTime();
	clauseid_t id;

	// Each node has associated two bitvectors containing the set of positive/negative
	// pivots present in all paths in its subgraph up to the root

	// Increased sets for taking into account pivots
	mpz_t incr_safe_lit_set_1; mpz_init(incr_safe_lit_set_1);
	mpz_t incr_safe_lit_set_2; mpz_init(incr_safe_lit_set_2);

	const size_t size = getGraphSize();
	mpz_t* safe_lit_set = new mpz_t [size];

	// Allocate root bitset
	const clauseid_t idd = getRoot()->getId();
	mpz_init(safe_lit_set[idd]);

	//DFS vector
	vector<clauseid_t>* DFSvec_ = new vector<clauseid_t>();
	vector<clauseid_t>& DFSvec = *DFSvec_;
	ProofNode * n = NULL;

	topolSortingBotUp(DFSvec);

	// To initialize pivots set to the set of the first resolvent
	for(size_t i=0; i< DFSvec.size(); i++)
	{
		id = DFSvec[i];
		n = getNode(id);
		assert(n);

		// Remove nodes left without resolvents
		if(!(isRoot( n )) && n->getNumResolvents()==0 )
		{
			if(n->getAnt1()!=NULL) n->getAnt1()->remRes( id );
			if(n->getAnt2()!=NULL) n->getAnt2()->remRes( id );
			if(isSetVisited1(id)) mpz_clear( safe_lit_set[id] );
			removeNode(id);
		}
		else if(!n->isLeaf())
		{
			clauseid_t id1 = n->getAnt1()->getId();
			clauseid_t id2 = n->getAnt2()->getId();
			Var piv = n->getPivot();
			int pos_piv = toInt(mkLit(piv,false));
			int neg_piv = toInt(mkLit(piv,true));

			short out = n->getAnt1()->hasOccurrenceBin(piv);
			assert( out!=-1 );
			// TODO guarantee positive occurrence pivot in ant1
			bool ant1_has_pos_occ_piv = ( out == 0 );

			// Enqueue antecedents
			assert( n->getAnt1() ); assert( n->getAnt2() );
			// 0 if no replacement, 1 if replacement by ant1, 2 if by ant2
			short replace = 0;
			// Check whether pivot present in all subgraph paths
			if( mpz_tstbit( safe_lit_set[id], pos_piv ) )
			{ if( ant1_has_pos_occ_piv ) replace = 1; else replace = 2; }
			else if( mpz_tstbit( safe_lit_set[id], neg_piv) )
			{ if( ant1_has_pos_occ_piv ) replace = 2; else replace = 1; }

			// A node marked to be replaced is left with the replacing
			// antecedent at ant1 and with ant2 set to NULL
			if( replace == 1 )
			{
				n->getAnt2()->remRes( id );
				n->setAnt2(NULL);
			}
			else if( replace == 2 )
			{
				n->getAnt1()->remRes( id );
				n->setAnt1(n->getAnt2());
				n->setAnt2(NULL);
			}

			// Update antecedents pivots sets
			// Propagate info to ant1
			if( replace == 1 )
			{
				if(!isSetVisited1(id1))
				{
					mpz_init( safe_lit_set[id1] );
					setVisited1(id1);
					mpz_set(safe_lit_set[id1], safe_lit_set[id]);
				}
				else
					mpz_and(safe_lit_set[id1], safe_lit_set[id1], safe_lit_set[id]);
			}
			// Propagate info to ant2
			if( replace == 2 )
			{
				if(!isSetVisited1(id2))
				{
					mpz_init( safe_lit_set[id2] );
					setVisited1(id2);
					mpz_set(safe_lit_set[id2], safe_lit_set[id]);
				}
				else
					mpz_and(safe_lit_set[id2], safe_lit_set[id2], safe_lit_set[id]);
			}
			// Propagate info to both antecedents if not replaced
			if( replace == 0 )
			{
				// Set pivot bit for propagation
				mpz_set( incr_safe_lit_set_1, safe_lit_set[id] );
				mpz_set( incr_safe_lit_set_2, safe_lit_set[id] );

				if(ant1_has_pos_occ_piv)
				{
					mpz_setbit( incr_safe_lit_set_1, pos_piv);
					mpz_setbit( incr_safe_lit_set_2, neg_piv);
				}
				else
				{
					mpz_setbit( incr_safe_lit_set_2, pos_piv);
					mpz_setbit( incr_safe_lit_set_1, neg_piv);
				}

				if(!isSetVisited1(id1))
				{
					mpz_init( safe_lit_set[id1] );
					setVisited1(id1);
					mpz_set(safe_lit_set[id1], incr_safe_lit_set_1);
				}
				else
					mpz_and(safe_lit_set[id1], safe_lit_set[id1], incr_safe_lit_set_1);

				if(!isSetVisited1(id2))
				{
					mpz_init( safe_lit_set[id2] );
					setVisited1(id2);
					mpz_set(safe_lit_set[id2], incr_safe_lit_set_2);
				}
				else
					mpz_and(safe_lit_set[id2], safe_lit_set[id2], incr_safe_lit_set_2);
			}
			// NOTE important, free memory for node id
			mpz_clear( safe_lit_set[id] );
		}
		else if(n->isLeaf())
		{
			// NOTE important, free memory for node id
			mpz_clear( safe_lit_set[id] );
		}
		else opensmt_error_();
	}

	delete(DFSvec_);
	delete [] safe_lit_set;
	mpz_clear(incr_safe_lit_set_1);
	mpz_clear(incr_safe_lit_set_2);
	resetVisited1();

	if ( verbose() > 1 ) { std::cerr << "; Recycling end, restructuring begin" << std::endl; }
	if ( verbose() > 1 )
	{
		uint64_t mem_used = memUsed();
		reportf( "; Memory used after recycling, before restructuring: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}

//	bool warning = false;
	// Restructuring, from leaves to root
	std::deque<clauseid_t>q;
	q.assign(leaves_ids.begin(),leaves_ids.end());
	do
	{
		id=q.front(); assert(id < getGraphSize());
		n=getNode(id); q.pop_front();
		//Node not visited yet
		if(n!=NULL && !isSetVisited2(id))
		{
			if(n->getAnt1()!=NULL && !isSetVisited2(n->getAnt1()->getId())){}
			else if(n->getAnt2()!=NULL && !isSetVisited2(n->getAnt2()->getId())){}
			// Mark node as visited if both antecedents visited
			else
			{
				setVisited2(id);
				//Non leaf node
				if(!(n->getAnt1()==NULL && n->getAnt2()==NULL))
				{
					assert(!(n->getAnt1()==NULL && n->getAnt2()!=NULL));
					// If replaced assign children to replacing node and remove
					if(n->hasBeenReplaced())
					{
						ProofNode* replacing = n->getAnt1();
						set<clauseid_t>& resolvents = n->getResolvents();
						for(set<clauseid_t>::iterator it = resolvents.begin(); it!=resolvents.end(); it++)
						{
							assert((*it)<getGraphSize());
							ProofNode* res = getNode((*it));
							assert(res);
							if(res->getAnt1() == n) res->setAnt1( replacing );
							else if (res->getAnt2() == n) res->setAnt2( replacing );
							else opensmt_error_();
							replacing->addRes((*it));
							assert(!isSetVisited2((*it)));
							// Enqueue resolvent
							q.push_back(*it);
						}
						replacing->remRes(id);
						assert(n==getNode(id));
						removeNode(id);
						assert(replacing->getNumResolvents() > 0);
						// NOTE extra check
						if(proofCheck() > 1) checkClause(replacing->getId());
					}
					else
					{
						assert(n->getAnt1()); assert (n->getAnt2());
						assert((n->getAnt1()->getAnt1()!=NULL && n->getAnt1()->getAnt2()!=NULL)
								|| (n->getAnt1()->getAnt1()==NULL && n->getAnt1()->getAnt2()==NULL));
						assert((n->getAnt2()->getAnt1()!=NULL && n->getAnt2()->getAnt2()!=NULL)
								|| (n->getAnt2()->getAnt1()==NULL && n->getAnt2()->getAnt2()==NULL));

						// NOTE not clear how this might happen
						if ( n->getAnt1() == n->getAnt2() )
						{
//							warning=true; // MB suspicious situation!
							ProofNode* replacing = n->getAnt1();
							set<clauseid_t>& resolvents = n->getResolvents();
							for(set<clauseid_t>::iterator it = resolvents.begin(); it!=resolvents.end(); it++)
							{
								assert((*it)<getGraphSize());
								ProofNode* res = getNode((*it));
								assert(res);
								if(res->getAnt1() == n) res->setAnt1( replacing );
								else if (res->getAnt2() == n) res->setAnt2( replacing );
								else opensmt_error_();
								replacing->addRes((*it));
								assert(!isSetVisited2((*it)));
								// Enqueue resolvent
								q.push_back(*it);
							}
							replacing->remRes(n->getId());
							assert(replacing->getNumResolvents() > 0);

							// We cannot have reached sink
							if(isRoot(n)) opensmt_error("trying to replace the root");
							removeNode(n->getId());
							if( replacing->getNumResolvents() == 0 ) removeTree( replacing->getId() );
							// NOTE extra check
							if(proofCheck() > 1) checkClause(replacing->getId());
						}
						else
						{
							//Look for pivot in antecedents
							bool piv_in_ant1=false, piv_in_ant2=false;
							short f1 = n->getAnt1()->hasOccurrenceBin(n->getPivot());
							if( f1 != -1 ) piv_in_ant1 = true;
							short f2 = n->getAnt2()->hasOccurrenceBin(n->getPivot());
							if( f2 != -1 ) piv_in_ant2 = true;
							assert( !(f1==1 && f2==1) && !(f1==0 && f2==0) );

							//Easy case: pivot still in both antecedents
							//Sufficient to propagate modifications via merge
							if(piv_in_ant1 && piv_in_ant2)
							{
								mergeClauses(n->getAnt1()->getClause(),n->getAnt2()->getClause(),n->getClause(),n->getPivot());
								for(set<clauseid_t>::iterator it = n->getResolvents().begin(); it != n->getResolvents().end(); it++ )
									if(getNode(*it) != NULL) q.push_back(*it);
								// NOTE extra check
								if(proofCheck() > 1) checkClause(n->getId());
							}
							//Second case: pivot not in ant1 or not in ant2
							//Remove resolution step, remove n, ant without pivots gains n resolvents
							else if(!piv_in_ant1 ||  !piv_in_ant2)
							{
								bool choose_ant1;
								//Pivot not in ant1 and not in ant2
								if(!piv_in_ant1 && !piv_in_ant2)
								{
									// Choose one of the two antecedents heuristically
									choose_ant1 = chooseReplacingAntecedent(n);
								}
								//Pivot not in ant1
								else if(!piv_in_ant1 && piv_in_ant2) choose_ant1=true;
								//Pivot not in ant2
								else if(piv_in_ant1 && !piv_in_ant2) choose_ant1=false;
								else opensmt_error_();

								ProofNode* replacing = (choose_ant1? n->getAnt1(): n->getAnt2());
								ProofNode* other = (choose_ant1? n->getAnt2(): n->getAnt1());
								replacing->remRes(id);
								other->remRes(id);

								set<clauseid_t>& resolvents = n->getResolvents();
								for(set<clauseid_t>::iterator it = resolvents.begin(); it!=resolvents.end(); it++)
								{
									assert((*it)<getGraphSize());
									ProofNode* res = getNode((*it));
									assert(res);
									if(res->getAnt1() == n) res->setAnt1( replacing );
									else if (res->getAnt2() == n) res->setAnt2( replacing );
									else opensmt_error_();
									replacing->addRes((*it));
									assert(!isSetVisited2((*it)));
									// Enqueue resolvent
									q.push_back(*it);
								}

								//We might have reached old sink
								//Case legal only if we have produced another empty clause
								//Substitute old sink with new
								if(isRoot(n))
								{
									assert( replacing->getClauseSize()==0 );
									setRoot( replacing->getId() );
									assert( n->getNumResolvents()==0 );
									assert( replacing->getNumResolvents()==0 );
								}
								removeNode(n->getId());
								if( other->getNumResolvents() == 0 ) removeTree( other->getId() );
								// NOTE extra check
								if(proofCheck() > 1) checkClause(replacing->getId());
							}
						}
					}
				}
				else
				{
					assert(n->getType()==clause_type::CLA_ORIG || n->getType()==clause_type::CLA_THEORY);
					assert(n->getNumResolvents() > 0);
					for(set<clauseid_t>::iterator it = n->getResolvents().begin(); it != n->getResolvents().end(); it++ )
						if(getNode(*it) != NULL) q.push_back(*it);
				}
			}
		}
	}
	while(!q.empty());
	resetVisited2();

	if( proofCheck() )
	{
		unsigned rem = cleanProofGraph( );
		if(rem > 0 ) std::cerr << "; Cleaned " << rem << " residual nodes" << std::endl;
		checkProof( true );
	}

	double endTime=cpuTime();

	if ( verbose() > 1 )
	{
		uint64_t mem_used = memUsed();
		reportf( "; Memory used after restructuring: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}

	////////////////////////////////////////////////////////////////////
	if( verbose() > 0 )
	{
		unsigned new_n_nodes=0;
		unsigned new_n_edges=0;
		for(unsigned i = 0; i < getGraphSize(); i++)
		{
			ProofNode* pn = getNode(i);
			if(pn != NULL){ new_n_nodes++; new_n_edges += pn->getNumResolvents(); }
		}
		cerr << "# RPI\t";
		cerr << "Nodes: " << new_n_nodes << "(-" << 100*((double)(num_nodes - new_n_nodes)/num_nodes) << "%)\t";
		cerr << "Edges: " << new_n_edges << "(-" << 100*((double)(num_edges - new_n_edges)/num_edges) << "%)\t";
		cerr << "Time: " << (endTime-initTime) << " s" << endl;
	}
	//////////////////////////////////////////////////////////////////

	return (endTime-initTime);
}

void ProofGraph::recycleUnits()
{
	if ( verbose() > 1 ) { cerr << "# " << "Recycle units begin" << endl; }
	if ( verbose() > 1 )
	{
		uint64_t mem_used = memUsed();
		reportf( "# Memory used before recycling: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}

	double initTime = cpuTime();
	bool some_transf_done = true;
	long curr_num_loops=0;

	RuleContext ra1,ra2;
	ProofNode* n;
	bool choose_ant1;

	set<clauseid_t> units_collected;
	std::deque<clauseid_t>q;
	clauseid_t id;
	// Main external loop
	while(some_transf_done)
	{
		// Enqueue leaves first
		q.assign(leaves_ids.begin(),leaves_ids.end());
		some_transf_done=false;
		do
		{
			id=q.front(); assert(id<getGraphSize());
			q.pop_front(); n=getNode(id);
			//Node not visited yet
			if(n!=NULL && !isSetVisited1(id))
			{
				// Wait if one antecedent is not visited yet;
				// the node will be enqueued anyway by that antecedent
				if(n->getAnt1()!=NULL && !isSetVisited1(n->getAnt1()->getId())){}
				else if(n->getAnt2()!=NULL && !isSetVisited1(n->getAnt2()->getId())){}
				// Mark node as visited if both antecedents visited
				else
				{
					setVisited1(id);
					// Enqueue resolvents
					for(set<clauseid_t>::iterator it = n->getResolvents().begin(); it != n->getResolvents().end(); it++ )
						if(getNode(*it) != NULL) q.push_back(*it);
					// Non leaf node
					if(!(n->getAnt1()==NULL && n->getAnt2()==NULL))
					{
						assert(n->getAnt1()); assert (n->getAnt2());
						assert((n->getAnt1()->getAnt1()!=NULL && n->getAnt1()->getAnt2()!=NULL) || (n->getAnt1()->getAnt1()==NULL && n->getAnt1()->getAnt2()==NULL));
						assert((n->getAnt2()->getAnt1()!=NULL && n->getAnt2()->getAnt2()!=NULL) || (n->getAnt2()->getAnt1()==NULL && n->getAnt2()->getAnt2()==NULL));

						//Look for pivot in antecedents
						bool piv_in_ant1=false, piv_in_ant2=false;

						short f1 = n->getAnt1()->hasOccurrenceBin(n->getPivot());
						if( f1 != -1 ) piv_in_ant1 = true;
						short f2 = n->getAnt2()->hasOccurrenceBin(n->getPivot());
						if( f2 != -1 ) piv_in_ant2 = true;
						assert( !(f1==1 && f2==1) && !(f1==0 && f2==0) );

						//Easy case: pivot still in both antecedents
						//Sufficient to propagate modifications via merge
						if(piv_in_ant1 && piv_in_ant2)
						{
							if(isSetVisited2(n->getAnt1()->getId()) || isSetVisited2(n->getAnt2()->getId()) )
							{
								mergeClauses(n->getAnt1()->getClause(),n->getAnt2()->getClause(),n->getClause(),n->getPivot());
								setVisited2(id);
							}

							// Check whether an antecedent is a unit clause
							// If so, v is replaced by the other antecedent
							// and the literal gets propagated down
							if(n->getAnt1()->getClauseSize() == 1 || n->getAnt2()->getClauseSize() == 1)
							{
								some_transf_done = true;
								bool choose_ant1;
								if(n->getAnt2()->getClauseSize() == 1) choose_ant1 = true;
								else choose_ant1 = false;

								ProofNode* replacing = (choose_ant1? n->getAnt1(): n->getAnt2());
								ProofNode* other = (choose_ant1? n->getAnt2(): n->getAnt1());
								// Keep track of the unit clause detached
								units_collected.insert(other->getId());

								replacing->remRes(id);
								other->remRes(id);

								set<clauseid_t>& resolvents = n->getResolvents();
								setVisited2(replacing->getId());

								for(set<clauseid_t>::iterator it = resolvents.begin(); it!=resolvents.end(); it++)
								{
									assert((*it)<getGraphSize());
									ProofNode* res = getNode((*it));
									assert(res);
									if(res->getAnt1() == n) res->setAnt1( replacing );
									else if (res->getAnt2() == n) res->setAnt2( replacing );
									else opensmt_error_();
									replacing->addRes((*it));
								}
								//We might have reached old sink
								//Substitute old sink with new
								if(isRoot(n))
								{
									setRoot( replacing->getId() );
									assert( n->getNumResolvents()==0 );
									assert( replacing->getNumResolvents()==0 );
								}
								removeNode(id);
							}
						}
						//Second case: pivot not in ant1 or not in ant2
						//Remove resolution step, remove n, ant without pivots gains n resolvents
						else if(!piv_in_ant1 ||  !piv_in_ant2)
						{
							//Pivot not in ant1 and not in ant2
							if(!piv_in_ant1 && !piv_in_ant2)
							{
								// Choose one of the two antecedents heuristically
								choose_ant1 = chooseReplacingAntecedent(n);
							}
							//Pivot not in ant1
							else if(!piv_in_ant1 && piv_in_ant2) choose_ant1=true;
							//Pivot not in ant2
							else if(piv_in_ant1 && !piv_in_ant2) choose_ant1=false;
							else opensmt_error_();

							ProofNode* replacing = (choose_ant1? n->getAnt1(): n->getAnt2());
							ProofNode* other = (choose_ant1? n->getAnt2(): n->getAnt1());

							replacing->remRes(id);
							other->remRes(id);

							set<clauseid_t>& resolvents = n->getResolvents();
							setVisited2(replacing->getId());

							for(set<clauseid_t>::iterator it = resolvents.begin(); it!=resolvents.end(); it++)
							{
								assert((*it)<getGraphSize());
								ProofNode* res = getNode((*it));
								assert(res);
								if(res->getAnt1() == n) res->setAnt1( replacing );
								else if (res->getAnt2() == n) res->setAnt2( replacing );
								else opensmt_error_();
								replacing->addRes((*it));
							}
							//We might have reached old sink
							//Substitute old sink with new
							if(isRoot(n))
							{
								setRoot( replacing->getId() );
								assert( n->getNumResolvents()==0 );
								assert( replacing->getNumResolvents()==0 );
							}
							removeNode(n->getId());
							if( other->getNumResolvents() == 0 ) removeTree( other->getId() );
						}
					}
				}
			}
		}
		while(!q.empty());
		// Visit vector
		resetVisited1();
		// To do only necessary merges, track modified nodes
		resetVisited2();

		// End loop
		curr_num_loops++;
	}

	//printClause(getRoot());
	// Readd each unit clause to restore the proof
	for(set<clauseid_t>::iterator it = units_collected.begin(); it != units_collected.end(); it++)
	{
		ProofNode* unit = getNode(*it);
		ProofNode* oldroot = getRoot();
		// NOTE is it possible to have multiple unit clauses containing the same literal?
		// If so, which one should be readded?
		if(oldroot->getClauseSize() == 0)
		{
			//cerr << "Clause not useful: "; printClause(unit);
		}
		else
		{
			//printClause(unit);
			ProofNode* newroot=new ProofNode(logic_, pmanager);
			newroot->initClause();
			if(produceInterpolants()) newroot->initIData();
			newroot->setAnt1(oldroot);
			newroot->setAnt2(unit);
			newroot->setType(clause_type::CLA_DERIVED);
			newroot->setPivot(var((unit->getClause())[0]));
			newroot->setId(graph.size());
			graph.push_back(newroot);
			unit->addRes(newroot->getId());
			oldroot->addRes(newroot->getId());
			//newroot given by resolution of root and unit over v pivot
			mergeClauses(oldroot->getClause(),unit->getClause(),newroot->getClause(),newroot->getPivot());
			// Update root
			setRoot(newroot->getId());
		}
	}
	assert(getRoot()->getClauseSize()==0);

	if( proofCheck() )
	{
		unsigned rem = cleanProofGraph( );
		if(rem > 0 ) cerr << "# Cleaned " << rem << " residual nodes" << endl;
		assert( rem == 0 );
		checkProof( true );
	}
	double endTime = cpuTime();

	if ( verbose() > 1 )
	{
		uint64_t mem_used = memUsed();
		reportf( "# Memory used after recycling: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}

	////////////////////////////////////////////////////////////////////
	if( verbose() > 0 )
	{
		unsigned new_n_nodes=0;
		unsigned new_n_edges=0;
		for(unsigned i = 0; i < getGraphSize(); i++)
		{
			ProofNode* pn = getNode(i);
			if(pn != NULL){ new_n_nodes++; new_n_edges += pn->getNumResolvents(); }
		}

		cerr << "# LU\t";
		cerr << "Nodes: " << new_n_nodes << "(-" << 100*((double)(num_nodes - new_n_nodes)/num_nodes) << "%)\t";
		cerr << "Edges: " << new_n_edges << "(-" << 100*((double)(num_edges - new_n_edges)/num_edges) << "%)\t";
		cerr << "Traversals: " << curr_num_loops << "\t";
		cerr << "Time: " << (endTime-initTime) << " s" << endl;
	}
	//////////////////////////////////////////////////////////////////
}


void ProofGraph::proofTransformAndRestructure(const double left_time, const int max_num_loops, bool do_transf,
        std::function<ApplicationResult(RuleContext&,RuleContext&)> handleRules)
{
    if (verbose() > 1) { std::cerr << "; " << "Proof transformation traversals begin" << std::endl; }
    if (verbose() > 1) {
        uint64_t mem_used = memUsed();
        reportf("; Memory used before proof transformation traversals: %.3f MB\n",
                mem_used == 0 ? 0 : mem_used / 1048576.0);
    }

    double init_time = cpuTime();
    assert(!(max_num_loops > 0 && left_time > 0));
    //Flag to check if in a loop at least a transformation has been applied
    bool some_transf_done;
    long curr_num_loops = 0;
    RuleContext ra1, ra2;
    std::deque<clauseid_t> q;
    clauseid_t id;
    // Main external loop
    do {
        // Enqueue leaves first
        q.assign(leaves_ids.begin(), leaves_ids.end());
        some_transf_done = false;
        do {
            id = q.front();
            assert(id < getGraphSize());
            q.pop_front();
            ProofNode * n = getNode(id);
            //Node not visited yet
            if (n != nullptr && !isSetVisited1(id)) {
                // Wait if one antecedent is not visited yet;
                // the node will be enqueued anyway by that antecedent
                if ((n->getAnt1() != nullptr && !isSetVisited1(n->getAnt1()->getId()))
                    || (n->getAnt2() != nullptr && !isSetVisited1(n->getAnt2()->getId()))) {
                    continue;
                }
                // ELSE, both antecedents ready, process the node
                // Mark node as visited
                setVisited1(id);
                // Non leaf node
                if ((n->getAnt1() != nullptr || n->getAnt2() != nullptr)) {
                    assert(n->getAnt1());
                    assert (n->getAnt2());
                    assert((n->getAnt1()->getAnt1() != nullptr && n->getAnt1()->getAnt2() != nullptr)
                           || (n->getAnt1()->getAnt1() == nullptr && n->getAnt1()->getAnt2() == nullptr));
                    assert((n->getAnt2()->getAnt1() != nullptr && n->getAnt2()->getAnt2() != nullptr)
                           || (n->getAnt2()->getAnt1() == nullptr && n->getAnt2()->getAnt2() == nullptr));

                    // NOTE not clear how this might happen
                    assert(n->getAnt1() != n->getAnt2());
                    if (n->getAnt1() == n->getAnt2()) {
                        opensmt_error("Bad proof structure!");
                    }
                    //Look for pivot in antecedents
                    short f1 = n->getAnt1()->hasOccurrenceBin(n->getPivot());
                    bool piv_in_ant1 = (f1 != -1);
                    short f2 = n->getAnt2()->hasOccurrenceBin(n->getPivot());
                    bool piv_in_ant2 = (f2 != -1);
                    assert(!(f1 == 1 && f2 == 1) && !(f1 == 0 && f2 == 0));
                    //Easy case: pivot still in both antecedents
                    //Sufficient to propagate modifications via merge
                    if (piv_in_ant1 && piv_in_ant2) {
                        for (clauseid_t clauseid : n->getResolvents()) {
                            if (getNode(clauseid) != nullptr) {
                                //assert(!isSetVisited1(clauseid));
                                q.push_back(clauseid);
                            }
                        }

                        if (isSetVisited2(n->getAnt1()->getId()) || isSetVisited2(n->getAnt2()->getId())) {
                            mergeClauses(n->getAnt1()->getClause(), n->getAnt2()->getClause(), n->getClause(),
                                         n->getPivot());
                            setVisited2(id);
                        }
                        // NOTE extra check
                        if (proofCheck() > 1) { checkClause(n->getId()); }

                        if (do_transf) {
                            //Look for rules applicability
                            getRuleContext(n->getAnt1()->getId(), n->getId(), ra1);
                            getRuleContext(n->getAnt2()->getId(), n->getId(), ra2);

                            auto chosen = handleRules(ra1, ra2);

                            rul_type app_rule = rNO;
                            if (chosen != ApplicationResult::NO_APPLICATION) {
                                clauseid_t A1_new_id = 0;
                                clauseid_t dupl_id = 0;
                                assert(chosen == ApplicationResult::APPLY_FIRST || chosen == ApplicationResult::APPLY_SECOND);
                                RuleContext & chosen_ra = chosen == ApplicationResult::APPLY_FIRST ? ra1 : ra2;
                                app_rule = chosen_ra.getType();
                                if (getNode(chosen_ra.getW())->getNumResolvents() > 1 && isSwapRule(app_rule)) {
                                    dupl_id = dupliNode(chosen_ra);
                                }
                                A1_new_id = ruleApply(chosen_ra);
                                some_transf_done = true;
                                // if(dupl_id != 0 && A1_new_id != 0) cerr << "A1 double on " << dupl_id << " " << A1_new_id << endl;

                                // NOTE see ProofGraphRules B3
                                // Mark v as modified
                                if (app_rule == rB1 || app_rule == rB2 || app_rule == rB2prime) { setVisited2(id); }
                                // Remember that in B3 v2 replaces v
                                if (app_rule == rB3) {
                                    setVisited2(chosen_ra.getV2());
                                }

                                // NOTE nodes might have been added on the fly by A1 and/or duplication
                                if (dupl_id != 0) {
                                    // The new node created by duplicating w has replaced w and will not be used elsewhere
                                    //visited_1.set(dupl_id); visited_2.reset(dupl_id);
                                }
                                if (A1_new_id != 0) {
                                    // The new node created by A1 is already updated and will not be used elsewhere
                                    //visited_1.set(A1_new_id); visited_2.reset(A1_new_id);
                                }
                            }
                            // NOTE extra check
                            if (proofCheck() > 1 && app_rule != rB3) { checkClause(n->getId()); }
                        }
                    } else {
                        //Second case: pivot not in ant1 or not in ant2
                        assert(!piv_in_ant1 || !piv_in_ant2);
                        //Remove resolution step, remove n, ant without pivots gains n resolvents
                        bool choose_ant1 = false;
                        if (!piv_in_ant1 && !piv_in_ant2) {
                            // Choose one of the two antecedents heuristically
                            choose_ant1 = chooseReplacingAntecedent(n);
                        } else {
                            choose_ant1 = !piv_in_ant1;
                        }
                        ProofNode * replacing = choose_ant1 ? n->getAnt1() : n->getAnt2();
                        ProofNode * other = choose_ant1 ? n->getAnt2() : n->getAnt1();

                        replacing->remRes(id);
                        other->remRes(id);

                        set<clauseid_t> & resolvents = n->getResolvents();
                        setVisited2(replacing->getId());

                        for (clauseid_t resolvent : resolvents) {
                            assert(resolvent < getGraphSize());
                            ProofNode * res = getNode(resolvent);
                            assert(res);
                            assert(res->getAnt1() == n || res->getAnt2() == n);
                            if (res->getAnt1() == n) { res->setAnt1(replacing); }
                            else if (res->getAnt2() == n) { res->setAnt2(replacing); }
                            else {opensmt_error("Error in the structure of the proof"); }
                            replacing->addRes(resolvent);
                            // Enqueue resolvent
                            q.push_back(resolvent);
                        }

                        //We might have reached old sink
                        //Case legal only if we have produced another empty clause
                        //Substitute old sink with new
                        if (isRoot(n)) {
                            assert(replacing->getClauseSize() == 0);
                            setRoot(replacing->getId());
                            assert(n->getNumResolvents() == 0);
                            assert(replacing->getNumResolvents() == 0);
                        }
                        removeNode(n->getId());
                        if (other->getNumResolvents() == 0) { removeTree(other->getId()); }
                        // NOTE extra check
                        if (proofCheck() > 1) { checkClause(replacing->getId()); }
                    }
                } else {
                    for (clauseid_t resolvent : n->getResolvents())
                        if (getNode(resolvent) != nullptr) { q.push_back(resolvent); }
                }
            }
        } while (!q.empty());
        // Visit vector
        resetVisited1();
        // To do only necessary merges, track modified nodes
        resetVisited2();

        // End loop
        curr_num_loops++;

        if (proofCheck() > 1) {
            std::cerr << "; Checking proof after loop " << curr_num_loops << std::endl;
            unsigned rem = cleanProofGraph();
            if (rem > 0) std::cerr << "; Cleaned " << rem << " residual nodes" << std::endl;
            checkProof(true);
        }
    }
    //Continue until
    // - max number of loops reached or timeout (in case of reduction)
    // - some transformation is done (in case of pivot reordering)
    while ((max_num_loops == -1 ? true : curr_num_loops < max_num_loops) &&
           (left_time == -1 ? true : (cpuTime() - init_time) <= left_time) &&
           (left_time != -1 || max_num_loops != -1 || some_transf_done));

    if (proofCheck()) {
        unsigned rem = cleanProofGraph();
        if (rem > 0) std::cerr << "; Cleaned " << rem << " residual nodes" << std::endl;
        //assert( rem == 0 );
        checkProof(true);
    }
    double endTime = cpuTime();

    if (verbose() > 1) {
        uint64_t mem_used = memUsed();
        reportf("; Memory used after proof transformation traversals: %.3f MB\n",
                mem_used == 0 ? 0 : mem_used / 1048576.0);
    }

    /////////////////////////////////////////////////////////////////////////////
    if (verbose() > 0) {
        unsigned new_n_nodes = 0;
        unsigned new_n_edges = 0;
        for (unsigned i = 0; i < getGraphSize(); i++) {
            ProofNode * pn = getNode(i);
            if (pn != nullptr) {
                new_n_nodes++;
                new_n_edges += pn->getNumResolvents();
            }
        }

        std::cerr << "; RE\t";
        if (num_nodes >= static_cast<int>(new_n_nodes)) {
            std::cerr << "Nodes: " << new_n_nodes << "(-" << 100 * ((double) (num_nodes - new_n_nodes) / num_nodes)
                      << "%)\t";
        }
        else {
            std::cerr << "Nodes: " << new_n_nodes << "(+" << 100 * ((double) (new_n_nodes - num_nodes) / num_nodes)
                      << "%)\t";
        }
        if (num_edges >= static_cast<int>(new_n_edges)) {
            std::cerr << "Edges: " << new_n_edges << "(-" << 100 * ((double) (num_edges - new_n_edges) / num_edges)
                      << "%)\t";
        }
        else {
            std::cerr << "Edges: " << new_n_edges << "(+" << 100 * ((double) (new_n_edges - num_edges) / num_edges)
                      << "%)\t";
        }
        std::cerr << "Traversals: " << curr_num_loops << "\t";
        std::cerr << "Time: " << (endTime - init_time) << " s" << std::endl;
    }
    ///////////////////////////////////////////////////////////////////////////////
}

void ProofGraph::proofPostStructuralHashing()
{
	if ( verbose() > 1 ) std::cerr << "; Post-processing structural hashing begin" << std::endl;
	if ( verbose() > 1 )
	{
		uint64_t mem_used = memUsed();
		reportf( "; Memory used before structural hashing: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}

	double initTime = cpuTime();
	vector<clauseid_t>q;
	clauseid_t id;
	ProofNode* n=NULL;
	// Map to associate node to its antecedents
	map< pair<clauseid_t,clauseid_t>, clauseid_t >* ants_map_ = new map< pair<clauseid_t,clauseid_t>, clauseid_t >;
	map< pair<clauseid_t,clauseid_t>, clauseid_t >& ants_map = *ants_map_;

	// NOTE Topological visit and node replacement on the fly
	// Guarantees that both replacing and replaced node subproofs have been visited
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
				// Non leaf node
				if(!n->isLeaf())
				{
					bool found = false;
					clauseid_t c1, c2;
					if(n->getAnt1()->getId() <= n->getAnt2()->getId())
					{ c1 = n->getAnt1()->getId(); c2 = n->getAnt2()->getId(); }
					else
					{ c2 = n->getAnt1()->getId(); c1 = n->getAnt2()->getId(); }
					// Look for pair <ant1,ant2>
					pair<clauseid_t, clauseid_t> ant_pair (c1,c2);
					map< pair<clauseid_t,clauseid_t>, clauseid_t >::iterator it = ants_map.find( ant_pair );
					found = ( it != ants_map.end() );
					// If pairs not found, add node to the map
					if( !found ) ants_map[ ant_pair ] = id ;
					// else replace node with existing one
					else
					{
						ProofNode* replacing = getNode( it->second );
						assert( replacing );
						// Move n children to replacing node
						for( set<clauseid_t>::iterator itt = n->getResolvents().begin(); itt != n->getResolvents().end(); itt++ )
						{
							assert((*itt)<getGraphSize());
							ProofNode* res = getNode((*itt));
							assert( res );
							if(res->getAnt1() == n) res->setAnt1( replacing );
							else if (res->getAnt2() == n) res->setAnt2( replacing );
							else opensmt_error_();
							replacing->addRes((*itt));
						}
						n->getAnt1()->remRes(id);
						n->getAnt2()->remRes(id);
						removeNode(id);
					}
				}
			}
		}
		else q.pop_back();
	}
	while(!q.empty());
	delete(ants_map_);
	resetVisited1();

	if( proofCheck() )
	{
		unsigned rem = cleanProofGraph( );
		if(rem > 0 ) std::cerr << "; Cleaned " << rem << " residual nodes" << std::endl;
		//assert( rem == 0 );
		checkProof( true );
	}
	double endTime = cpuTime();


	if ( verbose() > 1 )
	{
		uint64_t mem_used = memUsed();
		reportf( "; Memory used after structural hashing: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}

	/////////////////////////////////////////////////////////////////////////////
	if( verbose() > 0 )
	{
		unsigned new_n_nodes=0;
		unsigned new_n_edges=0;
		for(unsigned i = 0; i < getGraphSize(); i++)
		{
			ProofNode* pn = getNode(i);
			if(pn != NULL){ new_n_nodes++; new_n_edges += pn->getNumResolvents(); }
		}

		std::cerr << "; SH\t";
        std::cerr << "Nodes: " << new_n_nodes << "(-" << 100*((double)(num_nodes - new_n_nodes)/num_nodes) << "%)\t";
        std::cerr << "Edges: " << new_n_edges << "(-" << 100*((double)(num_edges - new_n_edges)/num_edges) << "%)\t";
        std::cerr << "Time: " << (endTime-initTime) << " s" << std::endl;
	}
	///////////////////////////////////////////////////////////////////////////////
}


namespace{
class LightVars {
public:

    template<typename TIt>
    LightVars(TIt begin, TIt end) {
        lights.insert(begin, end);
    }

    bool isLight(Var v) const { return lights.find(v) != lights.end(); }

private:
    std::unordered_set<Var> lights;
};

class LiftingVarsRuleHandler {
public:
    LiftingVarsRuleHandler(ProofGraph & pg, LightVars const & lv) : proofGraph(pg), lightVars(lv) {}

    ProofGraph::ApplicationResult operator()(RuleContext & ra1, RuleContext & ra2);

private:
    ProofGraph & proofGraph;
    LightVars const & lightVars;
};

using ApplicationResult = ProofGraph::ApplicationResult;


ApplicationResult LiftingVarsRuleHandler::operator()(RuleContext &ra1, RuleContext &ra2) {
    auto isUnordered = [this] (RuleContext const& ra) {
        Var lowerPivot = this->proofGraph.getNode(ra.getV())->getPivot();
        Var upperPivot = this->proofGraph.getNode(ra.getW())->getPivot();
        return this->lightVars.isLight(lowerPivot) && !this->lightVars.isLight(upperPivot);
    };
    bool enabled1 = ra1.enabled() && isUnordered(ra1);
    bool enabled2 = ra2.enabled() && isUnordered(ra2);
    if (!enabled1) {
        return enabled2 ? ApplicationResult::APPLY_SECOND : ApplicationResult::NO_APPLICATION;
    }
    // ra1 is enabled
    if (!enabled2) { return ApplicationResult::APPLY_FIRST; }
    // BOTH are enabled, pick better
    rul_type t1 = ra1.getType();
    rul_type t2 = ra2.getType();
    if (isCutRule(t1)) { return ApplicationResult::APPLY_FIRST; }
    if (isCutRule(t2)) { return ApplicationResult::APPLY_SECOND; }
    assert(isSwapRule(t1) && isSwapRule(t2));
    // Prefer simple swaps
    if (t1 == rA2) { return ApplicationResult::APPLY_FIRST; }
    if (t2 == rA2) { return ApplicationResult::APPLY_SECOND; }
    // No further rules, just pick first one
    return ApplicationResult::APPLY_FIRST;
}
}


void ProofGraph::liftVarsToLeaves(std::vector<Var> const & vars) {
    LightVars lightVars (vars.begin(), vars.end());
    LiftingVarsRuleHandler handler(*this, lightVars);
    proofTransformAndRestructure(-1, -1, true, handler);
}

void ProofGraph::replaceSubproofsWithNoPartitionTheoryVars(std::vector<Var> const & vars) {
    auto mustBeEliminated = [&vars](Var v) { return std::find(std::begin(vars), std::end(vars), v) != std::end(vars); };
    std::deque<clauseid_t> toProcess;
    toProcess.assign(this->leaves_ids.begin(), this->leaves_ids.end());
    resetVisited1();
    while (!toProcess.empty()) {
        clauseid_t current_id = toProcess.front();
        toProcess.pop_front();
        setVisited1(current_id);

        ProofNode * leaf = this->getNode(current_id);
        assert(leaf);
        assert(leaf->isLeaf());
        bool hasMixed = false;
        for (Var v : vars) {
            short present = leaf->hasOccurrenceBin(v);
            hasMixed |= (present != -1);
        }
        if (!hasMixed) { continue; }
        auto resolvents_ids = leaf->getResolvents();
        for (auto resolvent_id : resolvents_ids) {
            ProofNode * resolvent = this->getNode(resolvent_id);
            assert(resolvent);
            assert(mustBeEliminated(resolvent->getPivot())); // MB: While there is a problematic variable in the clause, all resolution steps must be on a problematic var
            if (!mustBeEliminated(resolvent->getPivot())) {
                opensmt_error("Error in post-processing in the proof: Lifting orphaned theory variables did not work properly");
            }
            // resolvent must be theory valid lemma, make it new leaf
            ProofNode * ant1 = resolvent->getAnt1();
            ProofNode * ant2 = resolvent->getAnt2();
            assert(ant1 && ant2);
            // only continue if both antecedents has been processed already!
            if (!isSetVisited1(ant1->getId()) || !isSetVisited1(ant2->getId())) {
                // This resolvent will be processed when the second antecedent is taken from the queue
                continue;
            }
            assert(ant1->getType() == clause_type::CLA_THEORY);
            assert(ant2->getType() == clause_type::CLA_THEORY);
            assert(ant1->isLeaf() && ant2->isLeaf());
            ant1->remRes(resolvent_id);
            ant2->remRes(resolvent_id);
            if (ant1->getNumResolvents() == 0) { this->removeNode(ant1->getId()); }
            if (ant2->getNumResolvents() == 0) { this->removeNode(ant2->getId()); }
            resolvent->setType(clause_type::CLA_THEORY);
            resolvent->setAnt1(nullptr);
            resolvent->setAnt2(nullptr);
            this->addLeaf(resolvent_id);
            toProcess.push_back(resolvent_id);
        }
    }
    resetVisited1();
}

