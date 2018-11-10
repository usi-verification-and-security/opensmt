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

#include <cstdio>
#include <iostream>
#include <fstream>


#ifdef PRODUCE_PROOF
#include "PG.h"
#include "BoolRewriting.h"


// Path interpolation
// Partitions   phi_1 ... phi_n
// Interpolants I_0 ... I_n
// Generation I_i = Itp(phi_1 ... phi_i | phi_{i+1} ... phi_n)
// Requirement  I_i /\ phi_{i+1} -> I_{i+1}
bool ProofGraph::producePathInterpolants ( vec<PTRef> &interpolants )
{
    assert ( interpolants.size( ) == 0 );
    unsigned nparts = logic_.getNofPartitions();

    if (nparts < 2)
    {
        opensmt_error ("Interpolation requires at least 2 partitions.");
        return false;
    }

    if (nparts == 2)
    {
        produceSingleInterpolant (interpolants);
        return true;
    }

    if ( verbose() ) cerr << "# Path interpolation " << endl;

    // Generate appropriate masks
    vec< ipartitions_t > configs;
    while (configs.size() <= logic_.getNofPartitions()+1)
        configs.push();
//    configs.resize (logic_.getNofPartitions() + 1, 0);

    // First interpolant is true -> all partitions in B
    for ( unsigned i = 1; i < configs.size(); i++ )
    {
        configs[i] = configs[i - 1];
        // Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
        setbit (configs[i], i);
    }

    produceMultipleInterpolants ( configs, interpolants );
    bool property_holds = true;

    if ( enabledInterpVerif() ) property_holds = verifyPathInterpolantsFromLeaves ( interpolants );

    return property_holds;
}

// Simultaneous abstraction
// Partitions   phi_1 ... phi_n
// Interpolants I_1 ... I_n
// Generation   I_i = Itp(phi_i | phi_1 ... phi_{i-1}, phi_{i+1} ... phi_n)
// Requirement  I_i /\ ... /\ I_n -> false
bool ProofGraph::produceSimultaneousAbstraction ( vec< PTRef > &interpolants )
{
    assert ( interpolants.size( ) == 0 );
    unsigned nparts = logic_.getNofPartitions();

    if (nparts < 2)
    {
        opensmt_error ("Interpolation requires at least 2 partitions.");
        return false;
    }

    if (nparts == 2)
    {
        produceSingleInterpolant (interpolants);
        return true;
    }

    if ( verbose() ) cerr << "# Simultaneous abstraction " << endl;

    // Generate appropriate masks
    vec< ipartitions_t > configs;
    while (configs.size() < logic_.getNofPartitions())
        configs.push();
//    configs.resize (logic_.getNofPartitions(), 0);

    for ( unsigned i = 0; i < configs.size(); i++ )
    {
        // Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
        setbit (configs[i], i + 1);
    }

    produceMultipleInterpolants ( configs, interpolants );
    bool property_holds = true;

    if ( enabledInterpVerif() ) property_holds = verifySimultaneousAbstraction ( interpolants );

    return property_holds;
}

// Generalized simultaneous abstraction
// Partitions   phi_1 ... phi_n
// Interpolants I_1 ... I_n
// Generation   for 1<=i<=n-1     I_i = Itp(phi_i | phi_1 ... phi_{i-1}, phi_{i+1} ... phi_n)
//              for i=n           I_n = Itp(phi_1 ... phi_{n-1} | phi_n)
// Requirement  I_i /\ ... /\ I_{n-1} -> I_n
bool ProofGraph::produceGenSimultaneousAbstraction ( vec< PTRef > &interpolants )
{
    assert ( interpolants.size( ) == 0 );
    unsigned nparts = logic_.getNofPartitions();

    if (nparts < 2)
    {
        opensmt_error ("Interpolation requires at least 2 partitions.");
        return false;
    }

    if (nparts == 2)
    {
        produceSingleInterpolant (interpolants);
        return true;
    }

    if ( verbose() ) cerr << "# Generalized simultaneous abstraction " << endl;

    // Generate appropriate masks
    vec< ipartitions_t > configs;
    while (configs.size() < nparts)
        configs.push();
//    configs.resize (nparts, 0);

    for ( unsigned i = 0; i < nparts - 1; i++ )
    {
        // Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
        setbit (configs[i], i + 1);
        // Update last configuration for I_n
        setbit (configs[nparts - 1], i + 1);
    }

    produceMultipleInterpolants ( configs, interpolants );
    bool property_holds = true;

    if ( enabledInterpVerif() ) property_holds = verifyGenSimultaneousAbstraction ( interpolants );

    return property_holds;
}

// State transition interpolation
// Partitions   phi_1 ... phi_n
// Interpolants I_0 ... I_n, J_1 ... J_n
// Generation   I_i = Itp(phi_1 ... phi_i | phi_{i+1} ... phi_n)
//              J_i = Itp(phi_i | phi_1 ... phi_{i-1}, phi_{i+1} ... phi_n)
// Requirement  I_i /\ J_{i+1} -> I_{i+1}
bool ProofGraph::produceStateTransitionInterpolants ( vec< PTRef > &interpolants )
{
    assert ( interpolants.size( ) == 0 );
    unsigned npart = logic_.getNofPartitions();

    if (npart < 2)
    {
        opensmt_error ("Interpolation requires at least 2 partitions.");
        return false;
    }

    if (npart == 2)
    {
        produceSingleInterpolant (interpolants);
        return true;
    }

    if ( verbose() ) cerr << "# State-transition interpolation " << endl;

    // Generate appropriate masks
    vec< ipartitions_t > configs;
    while (configs.size() < (2*npart) + 1)
        configs.push();
//    configs.resize ((2 * npart) + 1, 0);

    // All the path interpolants
    // First interpolant is true -> all partitions in B
    for ( unsigned i = 1; i < (npart + 1); i++ )
    {
        configs[i] = configs[i - 1];
        // Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
        setbit (configs[i], i);
    }

    // All the symmetric interpolants
    for ( unsigned i = (npart + 1); i < configs.size(); i++ )
    {
        // Set i_th bit to 1 (starting from bit 1, bit 0 is untouched)
        setbit (configs[i], (i - npart - 1) + 1);
    }

    produceMultipleInterpolants ( configs, interpolants );

    bool property_holds = true;

    if ( enabledInterpVerif() ) property_holds = verifyStateTransitionInterpolants ( interpolants );

    return property_holds;
}

void ProofGraph::produceConfigMatrixInterpolants (const vec< vec<int> > &configs, vec<PTRef> &interpolants)
{
    if ( verbose() ) cerr << "# General interpolation via configuration matrix " << endl;

    // Generate appropriate masks
    vec< ipartitions_t > parts;
    while (parts.size() < configs.size())
        parts.push();
//    parts.resize (configs.size(), 0);

    // First interpolant is true -> all partitions in B
    for ( unsigned i = 0; i < parts.size(); i++ )
    {
        for (unsigned j = 0; j < configs[i].size(); ++j)
        {
            // Set partitions[i] bit to 1 (starting from bit 1, bit 0 is untouched)
            // NOTE remember that partition ids are numbered from 0 in FunFrog!
            setbit ( parts[i], configs[i][j] + 1 );
        }
    }

    produceMultipleInterpolants ( parts, interpolants );
}

// Tree interpolation
// Partitions   phi_1 ... phi_n
// Subtrees     F_1   ... F_n
// Interpolants I_1 ... I_n
// Generation   I_i = Itp(F_i | all other formulae)
// Requirement  ( /\_(i,j) I_j /\ phi_i ) -> I_i
bool ProofGraph::produceTreeInterpolants (opensmt::InterpolationTree *it, vec<PTRef> &interpolants)
{
    if ( verbose() ) cerr << "# Tree interpolation " << endl;

    // NOTE some configurations might be empty,
    // if the corresponding nodes in the tree are not approximated
    // TODO

    // Generate appropriate masks
    // NOTE partition ids start from 1, parts vector from 0
    // parts[i] contains configuration mask for partition id i+1
    vec< ipartitions_t > parts;
    while (parts.size() < logic_.getNofPartitions())
        parts.push();
//    parts.resize (logic_.getNofPartitions(), 0);

    // Visit the tree in topological order bottom up and compute the configurations
    std::deque<opensmt::InterpolationTree *> q;
    set<int> visited;

    q.push_back (it);

    do
    {
        opensmt::InterpolationTree *node = q.front();
        q.pop_front();
        int pid = node->getPartitionId();

        //cerr << "Trying parent " << pid << endl;
        if (visited.find (pid) == visited.end())
        {
            bool children_visited = true;

            // Make sure all children have been visited, otherwise push them in the queue
            for ( set< opensmt::InterpolationTree * >::iterator it = node->getChildren().begin(); it != node->getChildren().end(); it++)
            {
                int cid =  (*it)->getPartitionId();

                if (visited.find (cid) == visited.end())
                {
                    children_visited = false;
                    q.push_back ((*it));
                    //cerr << "Enqueuing " << cid << endl;
                }
            }

            // All children have been visited
            if (children_visited)
            {
                //cerr << "Visiting " << pid << endl;
                visited.insert (pid);

                // Compute configuration for this node: A should include the node and the subtree rooted in it
                // In practice the mask is the logical or of the children masks plus the current node
                for ( set< opensmt::InterpolationTree * >::iterator it = node->getChildren().begin(); it != node->getChildren().end(); it++)
                {
                    int cid = (*it)->getPartitionId();
                    opensmt::orbit ( parts[pid - 1], parts[pid - 1], parts[cid - 1] );
                }

                setbit ( parts[pid - 1], pid );
                //cerr << "Partition ids in A for configuration " << pid-1 << ": ";
                //cerr << parts[pid-1].get_str(2) << " ";
                //cerr << endl;
            }
            else
            {
                //cerr << "Enqueuing " << pid << endl;
                q.push_back (node);
            }
        }
    }
    while (!q.empty());

    produceMultipleInterpolants ( parts, interpolants );
    bool property_holds = true;

    if ( enabledInterpVerif() ) property_holds = verifyTreeInterpolantsFromLeaves ( it, interpolants );

    return property_holds;
}

bool ProofGraph::producePathInterpolants ( vec<PTRef> &interpolants, const vec<ipartitions_t> &A_masks){
    bool propertySatisfied = true;
    // check that masks are subset of each other
#ifndef NDEBUG
    for(int i = 0; i < A_masks.size()-1; ++i) {
        assert((A_masks[i] & A_masks[i+1]) == A_masks[i]);
    }
#endif // NDEBUG
    for(int i = 0; i < A_masks.size(); ++i) {
        produceSingleInterpolant(interpolants, A_masks[i]);
//        if(verbose() > 1){
//            std::cerr << "; Interpolant for mask: " << A_masks[i] << " is: "
//                      << logic_.printTerm(interpolants[interpolants.size() - 1]);
//        }
        if(i > 0 && enabledInterpVerif()){
            PTRef previous_itp = interpolants[interpolants.size() - 2];
            PTRef next_itp = interpolants[interpolants.size() -1];
            PTRef movedPartitions = logic_.mkAnd(logic_.getPartitions(A_masks[i] ^ A_masks[i-1]));
            propertySatisfied &= logic_.implies(logic_.mkAnd(previous_itp, movedPartitions), next_itp);
            if (!propertySatisfied){
                std::cerr << "Path interpolation does not hold for:\n"
                             << "First interpolant: " << logic_.printTerm(previous_itp) << '\n'
                            << "Moved partitions: " << logic_.printTerm(movedPartitions) << '\n'
                            << "Second interpolant: " << logic_.printTerm(next_itp) << '\n';
            }
        }
    }
    assert(propertySatisfied);
    return propertySatisfied;
}

/**************** MAIN INTERPOLANTS GENERATION METHODS ************************/


void ProofGraph::produceSingleInterpolant ( vec<PTRef> &interpolants )
{
    ipartitions_t A_mask = 0;
    // Set 1_th bit to 1 (bit 0 is untouched)
    setbit (A_mask, 1);
    produceSingleInterpolant (interpolants, A_mask);
}

void ProofGraph::produceSingleInterpolant ( vec<PTRef> &interpolants, const ipartitions_t &A_mask)
{
    if ( verbose() ) cerr << "# Single interpolant " << endl;

#ifdef ITP_DEBUG
    PTRef tr_a = logic_.getPartitionA(A_mask);
    PTRef tr_b = logic_.getPartitionB(A_mask);

    char* fname;
    asprintf(&fname, "itp_problem_%s.smt2", A_mask.get_str(10).c_str());
    std::ofstream f;
    f.open(fname);
    logic_.dumpHeaderToFile(f);
    logic_.dumpFormulaToFile(f, tr_a);
    logic_.dumpFormulaToFile(f, tr_b);
    logic_.dumpChecksatToFile(f);
    f.close();
#endif

    // Check
    checkInterAlgo();

#ifdef FULL_LABELING
    // Track AB class variables and associate index to them in nodes bit masks
    computeABVariablesMapping ( A_mask );
#endif

    // NOTE generation of interpolants in CNF
    if ( interpolantInCNF() )
    {
#ifdef FULL_LABELING

        if ( usingMcMillanInterpolation() )
        {
            if ( verbose() > 0 ) cerr << "# Proof transformation for interpolants (partially) in CNF" << endl;

            fillProofGraph();
            proofTransformAndRestructure (-1, -1, true, &ProofGraph::handleRuleApplicationForCNFinterpolant);
            checkProof (true);
            // Normalize antecedents order ( for interpolation )
            normalizeAntecedentOrder();
            emptyProofGraph();
            printRuleApplicationStatus();
        }
        else
        {
            opensmt_warning ("Please set McMillan interpolation algorithm to generate interpolants in CNF");
        }

#else
        opensmt_warning ("Please compile with --enable-fulllabeling to enable proof transformation for interpolants in CNF");
#endif
    }
    // NOTE Preliminary application of A2 rules to strengthen/weaken the interpolant
    // Not compatible with interpolants in CNF
    //else if( restructuringForStrongerInterpolant() || restructuringForWeakerInterpolant() )
    // TODO enable proof reduction
    else if (0)
    {
        if ( verbose() > 0 && restructuringForStrongerInterpolant() ) cerr << "# Preliminary A2 rules application to strengthen interpolants" << endl;

        if ( verbose() > 0 && restructuringForWeakerInterpolant() ) cerr << "# Preliminary A2 rules application to weaken interpolants" << endl;

        fillProofGraph();
        // NOTE Only a couple of loops to avoid too much overhead
        proofTransformAndRestructure (-1, 2, true, &ProofGraph::handleRuleApplicationForStrongerWeakerInterpolant, A_mask);
        // Normalize antecedents order ( for interpolation )
        normalizeAntecedentOrder();
        emptyProofGraph();
    }

    // Clause and partial interpolant
    ProofNode *n;
    PTRef partial_interp;

    // Vector for topological ordering
    vector< clauseid_t > DFSv;
    // Compute topological sorting of graph
    topolSortingTopDown ( DFSv );
    size_t proof_size = DFSv.size();

    // check leaves for False clause
    // TODO do this in a better fucking way...

    for ( size_t i = 0 ; i < proof_size ; i++ )
    {
        n = getNode ( DFSv[ i ] );
        assert (n);

        if (n->isLeaf())
        {
            if (n->getType() != clause_type::CLA_ORIG && n->getType() != clause_type::CLA_THEORY) opensmt_error ( "Clause is not original nor theory" );

            vector<Lit> &cl = n->getClause();
            bool fal = false;

            if (cl.size() == 0) {
                opensmt_error("Empty clause found in interpolation\n");
                assert(false);
            }
            if (cl.size() == 1 && varToPTRef(var(cl[0])) == theory.getLogic().getTerm_false() && !sign(cl[0]))
                fal = true;

            if ((n->getType() == clause_type::CLA_ORIG && n->getClauseRef() == CRef_Undef) || fal)
            {
                //unit clause False exists, return degenerate interpolant
                icolor_t cc = getClauseColor (n->getInterpPartitionMask(), A_mask);
                Logic &logic = theory.getLogic();

                if (cc == I_A)
                    interpolants.push (logic.getTerm_false());
                else
                    interpolants.push (logic.getTerm_true());

                if(verbose())
                    cout << "; Degenerate interpolant" << endl;

                return;
            }
        }
    }

    if ( verbose() > 0 ) cerr << "# Generating interpolant " << endl;

    map<Var, icolor_t> *PSFunction = computePSFunction (DFSv, A_mask);

    // Traverse proof and compute current interpolant
    for ( size_t i = 0 ; i < proof_size ; i++ )
    {
        n = getNode ( DFSv[ i ] );
        assert (n);

        // Generate partial interpolant for clause i
        if (n->isLeaf())
        {
            if (n->getType() != clause_type::CLA_ORIG && n->getType() != clause_type::CLA_THEORY) opensmt_error ( "Clause is not original nor theory" );

            labelLeaf (n, A_mask, 0, PSFunction);

            /*
            cout << "; LEAF CLAUSE HAS LITERALS: " << endl;
            vector<Lit> &lala = n->getClause();
            for (int i = 0; i < lala.size(); ++i)
                cout << lala[i].x << ' ';
            cout << endl;
            */

            if (n->getType() == clause_type::CLA_ORIG)
            {
#ifdef ITP_DEBUG
                /*
                vector<Lit>& cl = n->getClause();
                for(int i = 0; i < cl.size(); ++i)
                    cerr << logic_.printTerm(thandler.varToTerm(var(cl[i]))) << "(" << cl[i].x << ") ";
                cerr << endl;
                */
#endif

#ifdef FULL_LABELING
                partial_interp = compInterpLabelingOriginal ( n, A_mask , 0, PSFunction);
#else
                partial_interp = compInterpLabelingOriginalSimple ( n, A_mask );
#endif
            }
            else
            {
                vec<DedElem> stub;
                for(int i = 0; i < theory.getDeductionVec().size(); ++i){
                    stub.push({theory.getDeductionVec()[i].deducedBy, l_Undef});
                }
                TSolverHandler* tmp = theory.getTSolverHandler_new(stub);
                vector<Lit> newvec;
                vector<Lit> &oldvec = n->getClause();

                for (int i = 0; i < oldvec.size(); ++i)
                    newvec.push_back (~oldvec[i]);

#ifdef ITP_DEBUG
                cout << "; ASSERTING LITS" << endl;
                vec<PTRef> tr_vec;
                Logic& logic = thandler.getLogic();
                for (int i = 0; i < newvec.size(); ++i) {
                    PTRef tr_vecel = thandler.varToTerm(var(newvec[i]));
                    tr_vec.push(sign(newvec[i]) ? logic.mkNot(tr_vecel) : tr_vecel);
                }
                PTRef tr_and = logic.mkAnd(tr_vec);
                printf("%s\n", logic.printTerm(tr_and));
#endif
                for (auto const & lit : newvec){
                    PTRef pt_r = varToPTRef(var(lit));
                    assert(logic_.isTheoryTerm(pt_r));
                    tmp->declareTerm(pt_r);
                }
                bool res = true;
                for (auto const & lit : newvec){
                    PTRef pt_r = varToPTRef(var(lit));
                    res = tmp->assertLit(PtAsgn(pt_r, sign(lit) ? l_False : l_True));
                }
                if (res) {
                    TRes tres = tmp->check(true);
                    res = (tres != TRes::UNSAT);
                }
                assert(!res);
                map<PTRef, icolor_t> ptref2label;
                vector<Lit>& cl = n->getClause();

                for(int i = 0; i < cl.size(); ++i)
                {
                    ptref2label[varToPTRef(var(cl[i]))] = getVarColor(n, var(cl[i]));
                }

                partial_interp = tmp->getInterpolant (A_mask, &ptref2label);
                delete tmp;
            }

            assert ( partial_interp != PTRef_Undef );
            n->setPartialInterpolant ( partial_interp );
            if (enabledPedInterpVerif())
                verifyPartialInterpolant(n, A_mask);
        }
        else
        {
#ifdef FULL_LABELING
            partial_interp = compInterpLabelingInner ( n );
#else
            partial_interp = compInterpLabelingInnerSimple ( n, A_mask );
#endif
            assert ( partial_interp != PTRef_Undef );
            n->setPartialInterpolant ( partial_interp );
        }
    }

    if (PSFunction != NULL) delete PSFunction;

    // Last clause visited is the empty clause with total interpolant
    assert (partial_interp == getRoot()->getPartialInterpolant());

    if( verbose() )
    {
        //getComplexityInterpolant(partial_interp);
        
        int nbool, neq, nuf, nif;
        theory.getLogic().collectStats(partial_interp, nbool, neq, nuf, nif);
        cerr << "; Number of boolean connectives: " << nbool << endl;
        cerr << "; Number of equalities: " << neq << endl;
        cerr << "; Number of uninterpreted functions: " << nuf << endl;
        cerr << "; Number of interpreted functions: " << nif << endl;
        
    }

    //if ( enabledInterpVerif() ) verifyPartialInterpolantFromLeaves( getRoot(), A_mask );
    if ( enabledInterpVerif() )
    {
        bool sound = theory.getLogic().verifyInterpolant (getRoot()->getPartialInterpolant(), A_mask );

        if(verbose())
        {
            if (sound) cout << "; Final interpolant is sound" << endl;
            else cout << "; Final interpolant is NOT sound" << endl;
        }
    }

    PTRef interpol = getRoot()->getPartialInterpolant();
    assert (interpol != PTRef_Undef);

    if(simplifyInterpolant() > 0 && logic_.isBooleanOperator(interpol)) {
        if(verbose() > 1) {
            std::cout << "Itp before rewriting max arity: \n" << logic_.printTerm(interpol) << "\n\n";
        }
        Map<PTRef,int,PTRefHash> PTRefToIncoming;
        ::computeIncomingEdges(logic_, interpol, PTRefToIncoming);
        interpol = ::rewriteMaxArity(logic_, interpol, PTRefToIncoming);
    }
    if (simplifyInterpolant() == 2 && logic_.isBooleanOperator(interpol) && !logic_.isNot(interpol)) {
        if(verbose() > 1) {
            std::cout << "Itp before aggressive simplifying: \n" << logic_.printTerm(interpol) << "\n\n";
        }
        Map<PTRef,int,PTRefHash> PTRefToIncoming;
        ::computeIncomingEdges(logic_, interpol, PTRefToIncoming);
        interpol = ::simplifyUnderAssignment(logic_, interpol, PTRefToIncoming);
    }

    if (simplifyInterpolant() == 3 && logic_.isBooleanOperator(interpol) && !logic_.isNot(interpol)) {
        if(verbose() > 1) {
            std::cout << "Itp before aggressive simplifying: \n" << logic_.printTerm(interpol) << "\n\n";
        }
        interpol = ::simplifyUnderAssignment_Aggressive(interpol, logic_);
    }

    interpolants.push ( interpol );

    if(verbose() > 1)
    {
        cout << "; Interpolant: " << theory.getLogic().printTerm(interpol) << endl;
    }
}

void ProofGraph::produceMultipleInterpolants ( const vec< ipartitions_t > &configs, vec<PTRef> &sequence_of_interpolants )
{
    /*  if( verbose() > 1 )
        {
            // Check configurations
            for(unsigned u = 0; u < configs.size(); u++)
            {
                cerr << "Partition ids in A for configuration " << u << ": ";
                cerr << configs[u].get_str(2) << " ";
                cerr << endl;
            }
        }*/
    // Check
    checkInterAlgo();

    if ( needProofStatistics() )
    {
#ifndef FULL_LABELING
        opensmt_warning ("Please compile with --enable-fulllabeling to enable proof-sensitive interpolation");
        return;
#endif
    }

    uint64_t mem_used = 0;

    if ( verbose() )
    {
        mem_used = memUsed();
        //reportff( "# Memory used before generating interpolants: %.3f MB\n",  mem_used == 0 ? 0 : mem_used / 1048576.0 );
    }

    assert ( sequence_of_interpolants.size( ) == 0 );

    // Clause and partial interpolant
    ProofNode *n;
    PTRef partial_interp;

    // Vector for topological ordering
    vector< clauseid_t > DFSv;
    // Compute topological sorting of graph
    topolSortingTopDown ( DFSv );
    size_t proof_size = DFSv.size();

    // Degenerate proof
    if (proof_size == 1) opensmt_error ("Degenerate proof, only empty clause - Cannot calculate interpolants");

    for ( unsigned curr_interp = 0; curr_interp < configs.size(); curr_interp ++ )
    {
        if ( verbose() > 0 ) cerr << "# Generating interpolant " << curr_interp << endl;

        const ipartitions_t &A_mask = configs[curr_interp];

#ifdef FULL_LABELING
        // Track AB class variables and associate index to them in nodes bit masks
        computeABVariablesMapping ( A_mask );
#endif

        map<Var, icolor_t> *PSFunction = computePSFunction (DFSv, A_mask);

        // Traverse proof and compute current interpolant
        for ( size_t i = 0 ; i < proof_size ; i++ )
        {
            n = getNode ( DFSv[ i ] );
            assert (n);

            // Generate partial interpolant for clause i
            if (n->isLeaf())
            {
                if (n->getType() != clause_type::CLA_ORIG) opensmt_error ( "Clause is not original" );

#ifdef FULL_LABELING
                partial_interp = compInterpLabelingOriginal ( n, A_mask, curr_interp , PSFunction);
                //if ( enabledPedInterpVerif() ) verifyPartialInterpolantFromLeaves( n, A_mask );
#else
                partial_interp = compInterpLabelingOriginalSimple ( n, A_mask );
#endif
            }
            else
            {
#ifdef FULL_LABELING
                partial_interp = compInterpLabelingInner ( n );
#else
                partial_interp = compInterpLabelingInnerSimple ( n, A_mask );
#endif
            }

            assert ( partial_interp != PTRef_Undef );
            n->setPartialInterpolant ( partial_interp );
        }

        if (PSFunction != NULL) delete PSFunction;

        // Last clause visited is the empty clause with total interpolant
        sequence_of_interpolants.push ( partial_interp );
        assert (partial_interp == getRoot()->getPartialInterpolant());

        if ( verbose() ) getComplexityInterpolant (partial_interp);

        if ( enabledInterpVerif() ) verifyPartialInterpolantFromLeaves ( getRoot(), A_mask );

        if ( verbose() )
        {
            mem_used = memUsed();
            //cerr << "# Interpolant: " << partial_interp << endl;
            //reportff( "# Memory used after generating %d interpolants: %.3f MB\n", curr_interp+1,  mem_used == 0 ? 0 : mem_used / 1048576.0 );
        }

        if ( printProofDotty( ) == 1 )
        {
            char buf[ 32 ];
            sprintf ( buf, "proof_interp_%d.dot", curr_interp );
            ofstream dotty ( buf );
            printProofAsDotty ( dotty, A_mask );
        }
    }
}

/********** SIMPLE INTERPOLATION WITHOUT FULL LABELING **********/

// Input: leaf clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
PTRef ProofGraph::compInterpLabelingOriginalSimple ( ProofNode *n, const ipartitions_t &A_mask )
{
    if (! ( usingMcMillanInterpolation( ) || usingPudlakInterpolation( ) || usingMcMillanPrimeInterpolation( ) ) )
        opensmt_error_();

    icolor_t clause_color = getClauseColor ( n->getInterpPartitionMask(), A_mask );
    // Original leaves can be only of class A or B
    assert ( clause_color == I_A || clause_color == I_B );

    PTRef partial_interp = PTRef_Undef;

    // Leaf belongs to A
    if ( clause_color == I_A )
    {
        // McMillan: compute clause restricted to AB
        if ( usingMcMillanInterpolation( ) )
        {
            vector< Lit > restricted_clause;
            icolor_t var_class;
            vector< Lit > &cl = n->getClause();
            const size_t size = cl.size( );

            for ( size_t i = 0 ; i < size ; i ++ )
            {
                var_class = getVarClass ( var (cl[i]), A_mask );

                if ( var_class == I_AB ) restricted_clause.push_back ( cl[i] );
            }

            size_t clause_size = restricted_clause.size( );

            //Create enode for the restricted clause
            if ( clause_size == 0 )
                //Partial interpolant is false in case of empty clause left
                partial_interp = logic_.getTerm_false( );
            else
            {
                PTRef lit = PTRef_Undef;
                vec<PTRef> or_args;

                for (size_t i = 0; i < clause_size; i++)
                {
                    lit = varToPTRef (var (restricted_clause[i]));

                    //Check polarity literal
                    if (sign (restricted_clause[i])) lit = logic_.mkNot (lit); //logic_.cons(lit));

                    //Build adding literals progressively
                    or_args.push (lit);
                }

                partial_interp = logic_.mkOr (or_args);
                assert (partial_interp != PTRef_Undef);
            }

//            cout << "McMillan leaf" << endl;
        }
        // Pudlak or McMillan': false
        else
        {
            partial_interp = logic_.getTerm_false(); //logic_.mkFalse( );
//          cout << "Pudlak or McMillan' leaf" << endl;
        }
    }
    // Leaf belongs to B
    else if ( clause_color == I_B )
    {
        //  McMillan': compute clause restricted to a
        if ( usingMcMillanPrimeInterpolation( ) )
        {
            vector< Lit > restricted_clause;
            icolor_t var_class;
            vector< Lit > &cl = n->getClause();
            const size_t size = cl.size( );

            for ( size_t i = 0 ; i < size ; i ++ )
            {
                var_class = getVarClass ( var (cl[i]), A_mask );

                if ( var_class == I_AB ) restricted_clause.push_back ( cl[i] );
            }

            size_t clause_size = restricted_clause.size( );

            // Create enode for the restricted clause
            if ( clause_size == 0 )
                // Partial interpolant is true (negation of false) in case of empty clause left
                partial_interp = logic_.getTerm_true(); //logic_.mkTrue( );
            else
            {
                // Remember that we are negating the restricted clause!
                // Literals change polarity and we build an and of literals

                PTRef lit = PTRef_Undef;
                vec<PTRef> and_args;

                for ( size_t i = 0 ; i < clause_size ; i++ )
                {
                    lit = varToPTRef ( var ( restricted_clause[i] ) );

                    if ( !sign ( restricted_clause[i] ) ) lit = logic_.mkNot (lit);

                    //Build adding literals progressively
                    and_args.push (lit);
                }

                partial_interp = logic_.mkAnd (and_args);
                assert (partial_interp != PTRef_Undef);
            }

//          cout << "McMillan' leaf" << endl;
        }
        // Pudlak or McMillan': true
        else
        {
            partial_interp = logic_.getTerm_true();
//          cout << "Pudlak or McMillan leaf" << endl;
        }
    }
    else opensmt_error ( "Clause has no color" );

    return partial_interp;
}

// Input: inner clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
PTRef ProofGraph::compInterpLabelingInnerSimple ( ProofNode *n, const ipartitions_t &A_mask )
{
    if (! ( usingMcMillanInterpolation( ) || usingPudlakInterpolation( ) || usingMcMillanPrimeInterpolation( ) ) )
        opensmt_error_();

    // Get antecedents partial interpolants
    PTRef partial_interp_ant1 = n->getAnt1()->getPartialInterpolant();
    PTRef partial_interp_ant2 = n->getAnt2()->getPartialInterpolant();
    assert ( partial_interp_ant1 != PTRef_Undef );
    assert ( partial_interp_ant2 != PTRef_Undef );

    PTRef partial_interp = PTRef_Undef;
    // Determine class pivot
    icolor_t pivot_class = getVarClass ( n->getPivot(), A_mask );

    // Pivot class A -> interpolant = interpolant of ant1 OR interpolant of ant2
    if ( pivot_class == I_A )
    {
        vec<PTRef> or_args;
        or_args.push (partial_interp_ant1);
        or_args.push (partial_interp_ant2);
        partial_interp = logic_.mkOr (or_args);
        assert (partial_interp != PTRef_Undef);
//        cout << "Class A inner" << endl;
    }
    // Pivot class B -> interpolant = interpolant of ant1 AND interpolant of ant2
    else if ( pivot_class == I_B )
    {
        vec<PTRef> and_args;
        and_args.push (partial_interp_ant1);
        and_args.push (partial_interp_ant2);
        partial_interp = logic_.mkAnd (and_args);
        assert (partial_interp != PTRef_Undef);
//        cout << "Class B inner" << endl;
    }
    // Pivot class AB ->
    // 1) Pudlak interpolant = (pivot OR interpolant of ant1) AND ((NOT pivot) OR interpolant of ant2)
    // 1) Alternative interpolant = ((NOT pivot) AND interpolant of ant1) OR (pivot AND interpolant of ant2)
    // 2) McMillan interpolant  = interpolant of ant1 AND interpolant of ant2
    // 3) McMillan' interpolant = interpolant of ant1 OR interpolant of ant2
    else if ( pivot_class == I_AB)
    {
        if ( usingPudlakInterpolation( ) )
        {
            // Find pivot occurrences in ant1 and ant2 and create enodes
            Var piv_ = n->getPivot();
            //cerr << "Inserting: " << thandler.varToEnode(piv_) << " " << piv_ << endl;
//          PTRef piv = thandler.varToEnode( piv_ );
            PTRef piv = varToPTRef ( piv_ );
            bool choose_alternative = false;

            if ( usingAlternativeInterpolant() ) choose_alternative = decideOnAlternativeInterpolation ( n );

            // Equivalent formula (I_1 /\ ~p) \/ (I_2 /\ p)
            if ( choose_alternative )
            {
                vec<PTRef> and1_args;
                and1_args.push (partial_interp_ant1);
                and1_args.push (logic_.mkNot (piv));
                PTRef and_1 = logic_.mkAnd (and1_args);
                vec<PTRef> and2_args;
                and2_args.push (partial_interp_ant2);
                and2_args.push (piv);
                PTRef and_2 = logic_.mkAnd (and2_args);
                vec<PTRef> or_args;
                or_args.push (and_1);
                or_args.push (and_2);
                PTRef partial_interp = logic_.mkOr (or_args);

//              PTRef and_1 = logic_.mkAnd( logic_.cons( partial_interp_ant1, logic_.cons( logic_.mkNot( logic_.cons( piv ) ) ) ) );
//              PTRef and_2 = logic_.mkAnd( logic_.cons( partial_interp_ant2, logic_.cons( piv ) ) );
//              partial_interp = logic_.mkOr( logic_.cons( and_1, logic_.cons( and_2 ) ) );
                // TODO ~piv \/ piv is not simplified, but should be!
                assert (partial_interp != logic_.getTerm_true());
                assert (partial_interp != PTRef_Undef);
//                cout << "Class AB Pudlak inner alternative" << endl;
//              assert(partial_interp != logic_.mkTrue());
            }
            // Standard interpolation (I_1 \/ p) /\ (I_2 \/ ~p)
            else
            {
                vec<PTRef> or1_args;
                or1_args.push (partial_interp_ant1);
                or1_args.push (piv);
                PTRef or_1 = logic_.mkOr (or1_args);

                vec<PTRef> or2_args;
                or2_args.push (partial_interp_ant2);
                or2_args.push (logic_.mkNot (piv));
                PTRef or_2 = logic_.mkOr (or2_args);

                vec<PTRef> args;
                args.push (or_1);
                args.push (or_2);
                partial_interp = logic_.mkAnd (args); // FIXME used to be a new declaration

//              PTRef or_1 = logic_.mkOr( logic_.cons( partial_interp_ant1, logic_.cons( piv ) ) );
//              PTRef or_2 = logic_.mkOr( logic_.cons( partial_interp_ant2, logic_.cons( logic_.mkNot( logic_.cons( piv ) ) ) ) );
//              partial_interp = logic_.mkAnd( logic_.cons( or_1, logic_.cons( or_2 ) ) );
                // TODO piv /\ ~piv is not simplified, but should be!
                assert (partial_interp != logic_.getTerm_false());
                assert (partial_interp != PTRef_Undef);
//              cout << "Class AB Pudlak inner" << endl;
            }
        }
        else if ( usingMcMillanInterpolation( ) )
        {
            vec<PTRef> args;
            args.push (partial_interp_ant1);
            args.push (partial_interp_ant2);

            partial_interp = logic_.mkAnd (args); // logic_.cons( partial_interp_ant1, logic_.cons( partial_interp_ant2 ) ) );
            assert (partial_interp != PTRef_Undef);
//            cout << "Class AB McMillan inner" << endl;
        }
        else if ( usingMcMillanPrimeInterpolation( ) )
        {
            vec<PTRef> args;
            args.push (partial_interp_ant1);
            args.push (partial_interp_ant2);
            partial_interp = logic_.mkOr (args); // logic_.cons( partial_interp_ant1, logic_.cons( partial_interp_ant2 ) ) );
            assert (partial_interp != PTRef_Undef);
//            cout << "Class AB McMillan' inner" << endl;
        }
        else opensmt_error ( "No interpolation algorithm");
    }
    else opensmt_error ( "Pivot has no class" );

    return partial_interp;
}

void ProofGraph::checkInterAlgo()
{
//    if(!usingPudlakInterpolation())
//        opensmt_error("Please use Pudlak (1) for boolean interpolation for now");
    if ( ! ( usingMcMillanInterpolation()
             || usingPudlakInterpolation()
             || usingMcMillanPrimeInterpolation()
             || usingPSInterpolation()
             || usingPSWInterpolation()
             || usingPSSInterpolation()
             || usingLabelingSuggestions()))
        opensmt_error ( "Please choose 0/1/2/3/4/5/6 as values for itp_bool_algo");

    if ( verbose() > 0 )
    {
        cerr << "# Using ";

        if ( usingPudlakInterpolation() )
            cerr << "Pudlak";
        else if ( usingMcMillanInterpolation() )
            cerr << "McMillan";
        else if ( usingMcMillanPrimeInterpolation() )
            cerr << "McMillan'";
        else if (  usingPSInterpolation() )
            cerr << "Proof-Sensitive";
        else if (  usingPSWInterpolation() )
            cerr << "Weak Proof-Sensitive";
        else if (  usingPSSInterpolation() )
            cerr << "Strong Proof-Sensitive";
        else if ( usingLabelingSuggestions() )
            cerr << "labeling suggestions";

        cerr << " for propositional interpolation" << endl;
    }
}


/********** FULL LABELING BASED INTERPOLATION **********/

#ifdef FULL_LABELING


void
ProofGraph::labelLeaf (ProofNode *n, const ipartitions_t &A_mask, unsigned num_config, map<Var, icolor_t> *PSFunction)
{
    // Proof Sensitive
    if (usingPSInterpolation()) setLeafPSLabeling (n, PSFunction);
    else if (usingPSWInterpolation()) setLeafPSWLabeling (n, PSFunction);
    else if (usingPSSInterpolation()) setLeafPSSLabeling (n, PSFunction);
    // McMillan's system
    else if ( usingMcMillanInterpolation( ) ) setLeafMcMillanLabeling ( n );
    // Symmetric system
    else if ( usingPudlakInterpolation( ) ) setLeafPudlakLabeling ( n );
    // McMillan's prime system
    else if ( usingMcMillanPrimeInterpolation( ) ) setLeafMcMillanPrimeLabeling ( n );
    // Labeling suggestions enabled
    else if ( usingLabelingSuggestions( ) ) setLabelingFromMap ( n, num_config );
    // Error
    else opensmt_error ( "No interpolation algorithm chosen" );
}

// Input: leaf clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
PTRef ProofGraph::compInterpLabelingOriginal ( ProofNode *n, const ipartitions_t &A_mask, unsigned num_config , map<Var, icolor_t> *PSFunction)
{
    // Then calculate interpolant
    icolor_t clause_color = getClauseColor ( n->getInterpPartitionMask(), A_mask );
#ifdef ITP_DEBUG
    cout << "Clause has mask " << n->getInterpPartitionMask() << ". Mask " << A_mask << endl;
    cout << "Clause has color " << clause_color << endl;
#endif

    if (clause_color == I_AB)
    {
        // Think of a heuristic for choosing the partition?
        clause_color = I_A;
    }

    // Original leaves can be only of class A or B
    assert ( clause_color == I_A || clause_color == I_B );

    PTRef partial_interp = PTRef_Undef;

    // Leaf belongs to A -> interpolant = leaf clause restricted to b
    if ( clause_color == I_A )
    {
        //Compute clause restricted to b

        vector< Lit > restricted_clause;
        // In labeling, classes and colors are distinct
        icolor_t var_class;
        icolor_t var_color;
        vector< Lit > &cl = n->getClause();

        const size_t size = cl.size( );

        for ( size_t i = 0 ; i < size ; i ++ )
        {
            Var v = var (cl[i]);
            var_class = getVarClass2 ( v );
            assert ( var_class == I_B || var_class == I_A || var_class == I_AB );

            if ( var_class == I_B || var_class == I_A ) var_color = var_class;
            else
            {
                // Determine color of AB variable
                if ( isColoredA ( n, v ) ) var_color = I_A;
                else if ( isColoredB ( n, v )  ) var_color = I_B;
                else if ( isColoredAB ( n, v ) ) var_color = I_AB;
                else opensmt_error ( "Variable " << v << " has no color in clause " << n->getId() );
            }

            if ( var_color == I_B ) restricted_clause.push_back ( cl[i] );
        }

        size_t clause_size = restricted_clause.size( );

        //Create enode for the restricted clause
        if ( clause_size == 0 )
            //Partial interpolant is false in case of empty clause left
            partial_interp = logic_.getTerm_false();
        else
        {
            PTRef lit;
            vec<PTRef> or_args;

            for (size_t i = 0; i < clause_size; i++)
            {
                lit = varToPTRef (var (restricted_clause[i]));

                //Check polarity literal
                if (sign (restricted_clause[i])) lit = logic_.mkNot (lit);

                //Build adding literals progressively
                or_args.push (lit);
            }

            partial_interp = logic_.mkOr (or_args);
        }
    }
    // Leaf belongs to B -> interpolant = negation of leaf clause restricted to a
    else if ( clause_color == I_B )
    {
        //Compute clause restricted to a

        vector< Lit > restricted_clause;
        // In labeling, classes and colors are distinct
        icolor_t var_class;
        icolor_t var_color;
        vector< Lit > &cl = n->getClause();

        const size_t size = cl.size( );

        for ( size_t i = 0 ; i < size ; i ++ )
        {
            Var v = var (cl[i]);
            var_class = getVarClass2 ( v );
            assert ( var_class == I_B || var_class == I_A || var_class == I_AB );

            if ( var_class == I_B || var_class == I_A ) var_color = var_class;
            else
            {
                // Determine color of AB variable
                if ( isColoredA ( n, v ) ) var_color = I_A;
                else if ( isColoredB ( n, v )  ) var_color = I_B;
                else if ( isColoredAB ( n, v ) ) var_color = I_AB;
                else opensmt_error ( "Variable " << v << " has no color in clause " << n->getId() );
            }

            if ( var_color == I_A ) restricted_clause.push_back ( cl[i] );
        }

        size_t clause_size = restricted_clause.size( );

        // Create enode for the restricted clause
        if ( clause_size == 0 )
            // Partial interpolant is true (negation of false) in case of empty clause left
            partial_interp = logic_.getTerm_true();
        else
        {
            PTRef lit;
            vec<PTRef> and_args;

            for ( size_t i = 0 ; i < clause_size ; i++ )
            {
                lit = varToPTRef ( var ( restricted_clause[i] ) );

                // Check polarity literal
                if ( !sign ( restricted_clause[i] ) )
                    lit = logic_.mkNot (lit);

                // Build adding literals progressively
                and_args.push (lit);
            }

            partial_interp = logic_.mkAnd (and_args);
        }
    }
    else opensmt_error ( "Clause has no color" );

    assert (partial_interp != PTRef_Undef);
    return partial_interp;
}

// Input: inner clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
PTRef ProofGraph::compInterpLabelingInner ( ProofNode *n )
{
    // Get antecedents partial interpolants
    PTRef partial_interp_ant1 = n->getAnt1()->getPartialInterpolant();
    PTRef partial_interp_ant2 = n->getAnt2()->getPartialInterpolant();
    assert ( partial_interp_ant1 != PTRef_Undef );
    assert ( partial_interp_ant2 != PTRef_Undef );

    PTRef partial_interp = PTRef_Undef;
    // Determine color pivot, depending on its color in the two antecedents
    icolor_t pivot_color = getPivotColor ( n );

    vec<PTRef> args;
    args.push (partial_interp_ant1);
    args.push (partial_interp_ant2);

    // Pivot colored a -> interpolant = interpolant of ant1 OR interpolant of ant2
    if ( pivot_color == I_A)
    {
        partial_interp = logic_.mkOr (args);
    }
    // Pivot colored b -> interpolant = interpolant of ant1 AND interpolant of ant2
    else if ( pivot_color == I_B )
    {
        partial_interp = logic_.mkAnd (args);
    }
    // Pivot colored ab -> interpolant = (pivot OR interpolant of ant1) AND ((NOT pivot) OR interpolant of ant2)
    // Alternative interpolant = ((NOT pivot) AND interpolant of ant1) OR (pivot AND interpolant of ant2)
    else if ( pivot_color == I_AB)
    {
        // Find pivot occurrences in ant1 and ant2 and create enodes
        Var piv_ = n->getPivot();
        //cerr << "Inserting: " << thandler.varToEnode(piv_) << " " << piv_ << endl;
        PTRef piv = varToPTRef ( piv_ );
        bool choose_alternative = false;

        if ( usingAlternativeInterpolant() ) choose_alternative = decideOnAlternativeInterpolation ( n );

        // Equivalent formula (I_1 /\ ~p) \/ (I_2 /\ p)
        if ( choose_alternative )
        {
            vec<PTRef> and1_args;
            vec<PTRef> and2_args;
            vec<PTRef> or_args;

            and1_args.push (partial_interp_ant1);
            and1_args.push (logic_.mkNot (piv));
            PTRef and_1 = logic_.mkAnd (and1_args);

            and2_args.push (partial_interp_ant2);
            and2_args.push (piv);
            PTRef and_2 = logic_.mkAnd (and2_args);

            if (logic_.isNot (and_1) && (logic_.getPterm (and_1)[0] == and_2))
                partial_interp = logic_.getTerm_true();
            else if (logic_.isNot (and_2) && (logic_.getPterm (and_2)[0] == and_1))
                partial_interp = logic_.getTerm_true();
            else
            {
                or_args.push (and_1);
                or_args.push (and_2);
                partial_interp = logic_.mkOr (or_args);

                // TODO ~piv \/ piv is not simplified, but should be!
                // now it should be
                assert (partial_interp != logic_.getTerm_true());
            }
        }
        // Standard interpolation (I_1 \/ p) /\ (I_2 \/ ~p)
        else
        {
            vec<PTRef> or1_args;
            vec<PTRef> or2_args;
            vec<PTRef> and_args;

            or1_args.push (partial_interp_ant1);
            or1_args.push (piv);
            PTRef or_1 = logic_.mkOr (or1_args);

            or2_args.push (partial_interp_ant2);
            or2_args.push (logic_.mkNot (piv));
            PTRef or_2 = logic_.mkOr (or2_args);

            if (logic_.isNot (or_1) && (logic_.getPterm (or_1)[0] == or_2))
                partial_interp = logic_.getTerm_false();
            else if (logic_.isNot (or_2) && (logic_.getPterm (or_2)[0] == or_1))
                partial_interp = logic_.getTerm_false();
            else
            {
                and_args.push (or_1);
                and_args.push (or_2);
                partial_interp = logic_.mkAnd (and_args);
                assert (partial_interp != logic_.getTerm_false());
            }

        }
    }
    else opensmt_error ( "Pivot has no color" );

    return partial_interp;
}

void
ProofGraph::setLeafPSLabeling (ProofNode *n, map<Var, icolor_t> *labels)
{
    assert (labels != NULL);
    //Reset labeling
    resetLabeling (n);

    vector<Lit> &cl = n->getClause();

    for (unsigned i = 0; i < cl.size(); ++i)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 (v);

        // Color AB class variables based on the map "labels"
        if (var_class == I_AB)
        {
            map<Var, icolor_t>::iterator it = labels->find (v);
            set<Var>::iterator itv = theory_only.find(v);
            assert (itv != theory_only.end() || it != labels->end());

            if (it->second == I_A)
                colorA (n, v);
            else
                colorB (n, v);
        }
        else if (var_class == I_A || var_class == I_B);
        else opensmt_error ("Variable has no class");
    }
}

void
ProofGraph::setLeafPSWLabeling (ProofNode *n, map<Var, icolor_t> *labels)
{
    assert (labels != NULL);
    //Reset labeling
    resetLabeling (n);

    vector<Lit> &cl = n->getClause();

    for (unsigned i = 0; i < cl.size(); ++i)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 (v);

        // Color AB class variables based on the map "labels"
        if (var_class == I_AB)
        {
            map<Var, icolor_t>::iterator it = labels->find (v);
            set<Var>::iterator itv = theory_only.find(v);
            assert (itv != theory_only.end() || it != labels->end());

            if (it->second == I_A)
                colorA (n, v);
            else
                colorAB (n, v);
        }
        else if (var_class == I_A || var_class == I_B);
        else opensmt_error ("Variable has no class");
    }
}

void
ProofGraph::setLeafPSSLabeling (ProofNode *n, map<Var, icolor_t> *labels)
{
    assert (labels != NULL);
    //Reset labeling
    resetLabeling (n);

    vector<Lit> &cl = n->getClause();

    for (unsigned i = 0; i < cl.size(); ++i)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 (v);

        // Color AB class variables based on the map "labels"
        if (var_class == I_AB)
        {
            map<Var, icolor_t>::iterator it = labels->find (v);
            set<Var>::iterator itv = theory_only.find(v);
            assert (itv != theory_only.end() || it != labels->end());

            if (it->second == I_A)
                colorAB (n, v);
            else
                colorB (n, v);
        }
        else if (var_class == I_A || var_class == I_B);
        else opensmt_error ("Variable has no class");
    }
}
void ProofGraph::setLeafPudlakLabeling ( ProofNode *n )
{
    // Reset labeling
    resetLabeling ( n );

    vector< Lit > &cl = n->getClause();

    for ( unsigned i = 0; i < cl.size(); i++)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 ( v );

        // Color AB class variables as ab
        if ( var_class == I_AB ) colorAB (n, v);
        else if ( var_class == I_A || var_class == I_B );
        else opensmt_error ( "Variable has no class" );
    }
}

void ProofGraph::setLeafMcMillanLabeling ( ProofNode *n )
{
    // Reset labeling
    resetLabeling (n);
    vector< Lit > &cl = n->getClause();

    for ( unsigned i = 0; i < cl.size(); i++)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 ( v );

        // Color AB class variables as b
        if ( var_class == I_AB ) colorB (n, v);
        else if ( var_class == I_A || var_class == I_B );
        else opensmt_error ( "Variable has no class" );
    }
}

void ProofGraph::setLeafMcMillanPrimeLabeling ( ProofNode *n )
{
    // Reset labeling
    resetLabeling (n);

    vector< Lit > &cl = n->getClause();

    for ( unsigned i = 0; i < cl.size(); i++)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 ( v );

        // Color AB class variables a if clause is in A
        if ( var_class == I_AB ) colorA (n, v);
        // Color AB class variables b if clause is in B
        else if ( var_class == I_A || var_class == I_B );
        else opensmt_error ( "Variable has no class" );
    }
}

void ProofGraph::setLabelingFromMap ( ProofNode *n, unsigned num_config )
{
    assert (vars_suggested_color_map);
    // Reset labeling
    resetLabeling (n);

    vector< Lit > &cl = n->getClause();

    for ( unsigned i = 0; i < cl.size(); i++)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 ( v );

        // Color AB class variables as a
        if ( var_class == I_AB )
        {
            // Retrieve correspondent Enode
            PTRef en = varToPTRef (v);
            std::map<PTRef, icolor_t> *col_map = (*vars_suggested_color_map)[num_config];
            assert (col_map);
            std::map<PTRef, icolor_t>::iterator it = col_map->find (en);

            if ( it == col_map->end() )
            {
                cerr << "Color suggestion for " << v << " not found; using Pudlak" << endl;
                colorAB (n, v);
            }
            else
            {
                icolor_t color = it->second;

                if (color == I_A) colorA (n, v);
                else if (color == I_B) colorB (n, v);
                else if (color == I_AB) colorAB (n, v);
                else opensmt_error_();
            }
        }
        else if ( var_class == I_A || var_class == I_B );
        else opensmt_error ( "Variable has no class" );
    }
}
#endif

#endif
