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


/************************* HELPERS ******************************/

bool ProofGraph::decideOnAlternativeInterpolation(ProofNode* n)
{
	// Get antecedents partial interpolants
	PTRef I1 = n->getAnt1()->getPartialInterpolant();
	PTRef I2 = n->getAnt2()->getPartialInterpolant();
	assert( I1 != PTRef_Undef ); assert( I2 != PTRef_Undef );
	bool I1_is_true = ( I1 == logic_.getTerm_true() );
	bool I2_is_true = ( I2 == logic_.getTerm_true() );
	bool I1_is_false = ( I1 == logic_.getTerm_false() );
	bool I2_is_false = ( I2 == logic_.getTerm_false() );
	bool I1_is_none = ( !I1_is_true && !I1_is_false );
	bool I2_is_none = ( !I2_is_true && !I2_is_false );

	// For some combinations of I1, I2, the alternative interpolant
	// has a smaller size!
	// Standard     (I1 \/ p ) /\ (I2 \/ ~p)
	// Alternative  (I1 /\ ~p) \/ (I2 /\ p)

	if(I1_is_false && I2_is_none) return true;
	if(I1_is_none && I2_is_false) return true;
	if(I1_is_false && I2_is_false) return true;
	return false;
}

#ifdef FULL_LABELING
void ProofGraph::computeABVariablesMapping( const ipartitions_t & A_mask )
{
	// Track AB class variables and associate index to them
	// NOTE class A has value -1, class B value -2, undetermined value -3, class AB has index bit from 0 onwards
	int AB_bit_index = 0;
	for( std::set<Var>::iterator nv = proof_variables.begin(); nv != proof_variables.end(); nv++ )
	{
		Var v = (*nv);
		icolor_t v_class = getVarClass( v, A_mask );
		if( v_class == I_A ){ AB_vars_mapping[v] = -1; }
		else if( v_class == I_B ){ AB_vars_mapping[v] = -2; }
		else if( v_class == I_AB ){ AB_vars_mapping[v] = AB_bit_index; AB_bit_index++; }
		else opensmt_error_();
	}
}

// Input: node, current interpolant partition masks for A and B
// e.g. 0---010 first partition in A
// node
// Output: returns node pivot color as a, b or ab
// depending on the colors in the node antecedents
icolor_t ProofGraph::getPivotColor( ProofNode* n )
{
	assert( !n->isLeaf() );
	Var v = n->getPivot();
	// In labeling, classes and colors are distinct
	icolor_t var_class = getVarClass2( v );

	// Update AB vars color vectors from antecedents
	updateColoringfromAnts(n);

	icolor_t var_color = I_UNDEF;
	// Determine if variable A-local, B-local or AB-common
	if ( var_class == I_A || var_class == I_B ) var_color = var_class;
	else if (  var_class == I_AB )
	{
		if( isColoredA( n,v ) ) var_color = I_A;
		else if ( isColoredB( n,v )  ) var_color = I_B;
		else if ( isColoredAB( n,v ) ) var_color = I_AB;
		else
		{
			icolor_t var_color_1=I_UNDEF;
			if( isColoredA( n,v ) ) var_color_1 = I_A;
			else if ( isColoredB( n,v )  ) var_color_1 = I_B;
			else if ( isColoredAB( n,v ) ) var_color_1 = I_AB;

			icolor_t var_color_2=I_UNDEF;
			if( isColoredA( n,v ) ) var_color_2 = I_A;
			else if ( isColoredB( n,v )  ) var_color_2 = I_B;
			else if ( isColoredAB( n,v ) ) var_color_2 = I_AB;

			cerr << "Pivot " << v << " has colors " << var_color_1 << " " << var_color_2 <<
					" in antecedents but no color in resolvent" << endl;
			opensmt_error_();
		}

		// Remove pivot from resolvent if class AB
		updateColoringAfterRes(n);
	}
	else opensmt_error( "Pivot " << v << " has no class" );

	return var_color;
}
#endif

// Input: variable, current interpolant partition masks for A and B
// e.g. 0---010 first partition in A
// Output: returns A-local , B-local or AB-common
icolor_t ProofGraph::getVarClass( Var v, const ipartitions_t & A_mask )
{
	// Get enode corresponding to variable
	//PTRef enode_var = thandler.varToTerm(v); //varToEnode( v );

	// TODO look at isAB methods in egraph
	//Determine mask corresponding to B
	ipartitions_t B_mask = ~A_mask;
	//Reset bit 0 to 0
	clrbit( B_mask, 0 );

	//Get partition mask variable
	//e.g. 0---0110 variable in first and second partition
	//const ipartitions_t & enode_mask = logic_.getIPartitions(enode_var);
	const ipartitions_t& enode_mask = logic_.getVarClassMask(v);
//	const ipartitions_t & enode_mask = enode_var->getIPartitions( );

	// Check if variable present in A or B
	const bool var_in_A = ( (enode_mask & A_mask) != 0 );
	const bool var_in_B = ( (enode_mask & B_mask) != 0 );
	assert( var_in_A || var_in_B );

	icolor_t var_class;
	// Determine if variable A-local, B-local or AB-common
	if ( var_in_A && !var_in_B ) var_class = I_A;
	else if ( !var_in_A && var_in_B ) var_class = I_B;
	else if (  var_in_A && var_in_B ) var_class = I_AB;
	else opensmt_error( "Variable has no class" );

	return var_class;
}

// Input: proof node, current interpolant partition masks for A and B
// e.g. 0---010 first partition in A
// Output: returns A or B
icolor_t ProofGraph::getClauseColor( const ipartitions_t & clause_mask, const ipartitions_t & A_mask )
{
	// Get partition mask clause
	// e.g. 0---0110 variable in first and second partition

	// TODO look at isAB methods in egraph
	//Determine mask corresponding to B
	ipartitions_t B_mask = ~A_mask;
	//Reset bit 0 to 0
	clrbit( B_mask, 0 );

	// Check if belongs to A or B
	const bool clause_in_A = ( (clause_mask & A_mask) != 0 );
	const bool clause_in_B = ( (clause_mask & B_mask) != 0 );
	assert( clause_in_A || clause_in_B );

	icolor_t clause_color = I_A;

	// Determine if clause belongs to A or B
	if( clause_in_A && !clause_in_B ) clause_color = I_A;
	else if( !clause_in_A && clause_in_B ) clause_color = I_B;
	else if( clause_in_A && clause_in_B ) clause_color = I_AB;
	else opensmt_error( "Clause has no color" );

	return clause_color;
}


map<Var, icolor_t>*
ProofGraph::computePSFunction(vector< clauseid_t >& DFSv, const ipartitions_t& A_mask)
{
	size_t proof_size = DFSv.size();

	map<Var, icolor_t> *labels = NULL;
	ProofNode *n;
	if(needProofStatistics())
	{
		labels = new map<Var, icolor_t>();

		time_t after, before;
		time(&before);
		
		map<Var, int> occ_a, occ_b;
		int aclauses, bclauses;
		aclauses = bclauses;
		for(size_t i = 0; i < proof_size; ++i)
		{
			n = getNode(DFSv[i]); assert(n);
			if(!n->isLeaf()) continue;
			if(n->getType() != CLAORIG)
			{
		            if(n->getType() != CLATHEORY)
     			        opensmt_error( "Clause is not original" );
			}
			icolor_t col = getClauseColor(n->getInterpPartitionMask(), A_mask);
			vector<Lit>& lits = n->getClause();
			if(!lits.empty())
			{
				for(int i = 0; i < int(lits.size()); ++i)
				{
					int v = var(lits.at(i));
					icolor_t vclass = getVarClass2(v);
					if(vclass != I_AB) continue;
					if(col == I_A)
					{
						++aclauses;
						++occ_a[v];
						if(occ_b.find(v) == occ_b.end())
							occ_b[v] = 0;
					}
					else if(col == I_B)
					{
						++bclauses;
						++occ_b[v];
						if(occ_a.find(v) == occ_a.end())
							occ_a[v] = 0;
					}
				}
			}
		}
		assert(occ_a.size() == occ_b.size());
		int avars, bvars, aevars, bevars;
		avars = bvars = aevars = bevars = 0;
		map<Var, int>::iterator it;
		srand(time(NULL));
		for(it = occ_a.begin(); it != occ_a.end(); ++it)
		{
			Var v = it->first;
			int qtta = it->second;
			int qttb = occ_b.find(v)->second;
			bool fa = true; //suppose label is A
			if(qtta == qttb)
			{
				//if(rand() % 2) fa = false; //random == 1, label B (breaks path-interpolation property!!!)
				fa = false;
			}
			else if(qttb > qtta) //b greater label B
				fa = false;

			if(fa)
			{
				if(qtta > qttb) ++avars; else ++aevars;
				labels->insert(pair<Var, icolor_t>(v, I_A));
			}
			else
			{
				if(qttb > qtta) ++bvars; else ++bevars;
				labels->insert(pair<Var, icolor_t>(v, I_B));
			}
		}
		cout << avars << " A> " << aevars << " A=\n" << bvars << " B> " << bevars << " B=" << endl;
		///////////////////////////////////////////////////////////
		time(&after);
		cout << "Time spent computing PS labeling function: " << difftime(after, before) << "s" << endl;
	}

	return labels;
}

#endif
