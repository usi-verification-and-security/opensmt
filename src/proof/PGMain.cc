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


// Manipulates proofs
void ProofGraph::printProofGraph( )
{
	assert( printProofDotty() > 0);
	// Fill proof
	fillProofGraph();
	//Print original proof
	if( verbose() > 0 ) cerr << "# Outputting dotty proof" << endl;
	ofstream dotty( "proof.dot", ofstream::out | ofstream::trunc);
	printProofAsDotty( dotty );
	emptyProofGraph();
}

void ProofGraph::transfProofForReduction( )
{
	// Initialize C-random number generator with fixed seed to ensure reproducibility
	srand(config.getRandomSeed());
	// Fill proof
	fillProofGraph();

	// Time left for transformation
	double solvingTime = cpuTime( );

//	size_t size=0;
	int numnodes=0;
	int numedges=0;
	int numleaves=0;
	int numvars=0;
	double avgdeg=0;
	int maxclasize=0;
	double avgclasize=0;
	int numunary=0;
//	double varclasize=0;

	if ( verbose() )
	{
		getGraphInfo( );

//		size = graph.size( );
		numnodes = num_nodes;
		numedges = num_edges;
		numleaves = num_leaves;
		numvars = proof_variables.size();
		avgdeg = (double)numedges / (double)numnodes;
		maxclasize = max_cla_size;
		avgclasize = av_cla_size;
		numunary = num_unary;
//		varclasize = var_cla_size;
	}

	double time=0;

	time = doReduction( solvingTime );

	if( proofCheck() )
	{
		checkProof( true );
		unsigned rem = cleanProofGraph( );
		if(verbose() > 0) cerr << "# Cleaned " << rem << " residual nodes"  << endl;
		if(rem > 0) checkProof( true );
	}

	if ( verbose() > 0 )
	{
		getGraphInfo( );

		double perc_nodes=(((double)num_nodes-(double)numnodes)/(double)numnodes)*100;
		double perc_edges=(((double)num_edges-(double)numedges)/(double)numedges)*100;
		double perc_leaves=(((double)num_leaves-(double)numleaves)/(double)numleaves)*100;
		cerr << "#" << endl;
		cerr << "# ------------------------------------" << endl;
		cerr << "# PROOF GRAPH REDUCTION STATISTICS    " << endl;
		cerr << "# ------------------------------------" << endl;
		cerr << "# Structural properties" << endl;
		cerr << "# ---------------------" << endl;
		cerr << "# Nominal num proof variables: ";
		fprintf( stderr, "%-10d\n", num_vars_limit );
		cerr << "# Actual num proof variables.: ";
		fprintf( stderr, "%-10d %-10d\n", numvars, (int)proof_variables.size() );
		cerr << "# Nodes......................: ";
		fprintf( stderr, "%-10d %-10d\n", numnodes, num_nodes );
		cerr << "# Nodes variation............: ";
		fprintf( stderr, "%-9.2f %%\n", perc_nodes );
		cerr << "# Leaves.....................: ";
		fprintf( stderr, "%-10d %-10d\n", numleaves, num_leaves );
		cerr << "# Leaves variation...........: ";
		fprintf( stderr, "%-9.2f %%\n", perc_leaves );
		cerr << "# Edges......................: ";
		fprintf( stderr, "%-10d %-10d\n", numedges, num_edges );
		cerr << "# Edges variation............: ";
		fprintf( stderr, "%-9.2f %%\n", perc_edges );
		//cerr << "# Graph vector size..........: ";
		//fprintf( stderr, "%-10ld %-10ld\n", size, graph.size( ) );
		cerr << "# Average degree.............: ";
		fprintf( stderr, "%-10.2f %-10.2f\n", avgdeg, (double)num_edges / (double)num_nodes );
		cerr << "# Unary clauses..............: ";
		fprintf( stderr, "%-10d %-10d\n", numunary, num_unary );
		cerr << "# Max clause size............: ";
		fprintf( stderr, "%-10d %-10d\n", maxclasize, max_cla_size );
		cerr << "# Average clause size........: ";
		fprintf( stderr, "%-10.2f %-10.2f\n", avgclasize, av_cla_size );
		//cerr << "# Variance clause size.......: ";
		//fprintf( stderr, "%-10.2f %-10.2f\n", varclasize, var_cla_size );
		cerr << "# -------------------------" << endl;
		cerr << "# Transformation statistics" << endl;
		cerr << "# -------------------------" << endl;
		cerr << "# Graph building time........: " << building_time << " s" << endl;
		cerr << "# Transformation time........: " << time << " s" << endl;
		//cerr << "# Duplications...............: " << num_dup << endl;
		//cerr << "# Node additions due to A1...: " << num_node_add_A1 << endl;
		cerr << "# ---------------------------" << endl;
		cerr << "# Rules application statistics" << endl;
		cerr << "# ---------------------------" << endl;
		cerr << "# A1.........................: " << A1 << endl;
		cerr << "# A1'........................: " << A1prime << endl;
		cerr << "# A1 to B....................: " << A1B << endl;
		cerr << "# A2.........................: " << A2 << endl;
		cerr << "# A2 to B....................: " << A2B << endl;
		cerr << "# A2 unary...................: " << A2U << endl;
		cerr << "# B1.........................: " << B1 << endl;
		cerr << "# B2'........................: " << B2prime << endl;
		cerr << "# B2.........................: " << B2 << endl;
		cerr << "# B3.........................: " << B3 << endl;
		cerr << "# Duplications...............: " << duplications << endl;
		cerr << "# Swap ties..................: " << swap_ties << endl;
		cerr << "# ---------------------------" << endl;
	}

	/*	if ( verbose() > 0 )
	{
		uint64_t mem_used = memUsed();
		reportff( "# Memory used after reducing the proof: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
	}*/

	if( printProofDotty() == 1 )
	{
		//Print reduced proof
		if( verbose() > 0 ) cerr << "# Outputting dotty proof reduced" << endl;
		ofstream dottyred( "proof_reduced.dot" );
		printProofAsDotty( dottyred );
	}
	// TODO return reduced proof in SMTLIB2 format
	// Normalize antecedents order ( for interpolation )
	normalizeAntecedentOrder();
	// Empty proof
	emptyProofGraph();
}

// Performs reduction
double ProofGraph::doReduction(double solving_time) {
    if (enabledTransfTraversals()) {
        if ((ratioReductionSolvingTime() > 0 && reductionTime() > 0) ||
            (ratioReductionSolvingTime() > 0 && numGraphTraversals() > 0) ||
            (reductionTime() > 0 && numGraphTraversals() > 0) ||
            (ratioReductionSolvingTime() == 0 && reductionTime() == 0 && numGraphTraversals() == 0)) opensmt_error(
                "Please set either ratio or time for reduction or number of proof traversals");
    }
    if (reductionLoops() == 0) opensmt_error("Please set number of global reduction loops to at least 1");

    //Transformation time calculation
    double time_init = 0;
    double time_end = 0;
    double red_time = 0;
    //Number of inner transformation loops
    //-1 for exhaustiveness
    //int num_transf_loops=0; // MB: not used?
    //Number of outer transformation loops
    //useful for alternation with recycle pivots
    int num_global_reduction_loops = 0;
    // Time available for transformations
    // -1 for exhaustiveness
    double ratio;

    if (ratioReductionSolvingTime() > 0) {
        // Ratio transformation time/solving time
        ratio = ratioReductionSolvingTime();
        red_time = ratio * solving_time;
    } else if (reductionTime() > 0) {
        red_time = reductionTime();
    }

    //For each outer loop, recycle pivots algorithm is executed, followed by a certain
    //number of transformation loops, or by a single restructuring loop

    //Each global loop is given an equal fraction of available time
    num_global_reduction_loops = reductionLoops();
    if (verbose() > 0) {
        cerr << "# Compressing proof, " << num_global_reduction_loops << " global iteration(s) " << endl;
        if (enabledPushDownUnits()) cerr << "# preceded by LowerUnits" << endl;
        cerr << "# Each global iteration consists of: " << endl;
        if (enabledStructuralHashing()) cerr << "# StructuralHashing" << endl;
        if (enabledRecyclePivots()) cerr << "# RecyclePivotsWithIntersection" << endl;
        if (enabledTransfTraversals()) {
            cerr << "# ReduceAndExpose ";
            if (ratioReductionSolvingTime() > 0 || reductionTime() > 0)
                cerr << "with overall timeout " << red_time << " sec(s) " << endl;
            else if (numGraphTraversals() > 0)
                cerr << "with " << numGraphTraversals() << " graph traversal(s) " << endl;
        }
        cerr << "#" << endl;
    }
    double spent_time = 0, i_time = 0;

    time_init = cpuTime();
    if (enabledPushDownUnits()) recycleUnits();
    for (int k = 1; k <= num_global_reduction_loops; k++) {
        if (verbose() > 0) cerr << "# Global iteration " << k << endl;
        i_time = cpuTime();
        if (switchToRPHashing()) {
            if (enabledRecyclePivots()) recyclePivotsIter();
            if (enabledStructuralHashing()) proofPostStructuralHashing();
        } else {
            if (enabledStructuralHashing()) proofPostStructuralHashing();
            if (enabledRecyclePivots()) recyclePivotsIter();
        }
        spent_time = cpuTime() - i_time;
        // Not really meaningful to do graph traversals in the last global loop
        if (enabledTransfTraversals() && k <= num_global_reduction_loops - 1) {
            auto handleRuleApplication = [this](RuleContext & ra1, RuleContext & ra2) {
                return this->handleRuleApplicationForReduction(ra1, ra2);
            };
            if (ratioReductionSolvingTime() > 0 || reductionTime() > 0) {
                // Available time = global loop timeout - time used for recycle pivots
                // Already out of time for transformation rules
                if (red_time - spent_time <= 0) { continue; }
                proofTransformAndRestructure(red_time - spent_time, -1, true, handleRuleApplication);
            }
            if (numGraphTraversals() > 0) {
                proofTransformAndRestructure(-1, numGraphTraversals(), true, handleRuleApplication);
            }
        }
    }
    time_end = cpuTime();
    return time_end - time_init;
}
