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

#include "BoolRewriting.h"
#include "OsmtInternalException.h"
#include "VerificationUtils.h"

#include <cstdio>
#include <iostream>
#include <fstream>


// Path interpolation
// Partitions   phi_1 ... phi_n
// Interpolants I_0 ... I_n
// Generation I_i = Itp(phi_1 ... phi_i | phi_{i+1} ... phi_n)
// Requirement  I_i /\ phi_{i+1} -> I_{i+1}
bool ProofGraph::producePathInterpolants ( vec<PTRef> &interpolants )
{
    assert ( interpolants.size( ) == 0 );
    unsigned nparts = pmanager.getNofPartitions();

    if (nparts < 2)
    {
        throw OsmtApiException("; Interpolation requires at least 2 partitions.");
    }

    if (nparts == 2)
    {
        produceSingleInterpolant (interpolants);
        return true;
    }

    if ( verbose() ) std::cerr << "; Path interpolation " << '\n';

    // Generate appropriate masks
    std::vector< ipartitions_t > configs;
    configs.resize (pmanager.getNofPartitions() + 1, 0);

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
    unsigned nparts = pmanager.getNofPartitions();

    if (nparts < 2)
    {
        throw OsmtApiException("; Interpolation requires at least 2 partitions.");
    }

    if (nparts == 2)
    {
        produceSingleInterpolant (interpolants);
        return true;
    }

    if ( verbose() ) std::cerr << "; Simultaneous abstraction " << '\n';

    // Generate appropriate masks
    std::vector< ipartitions_t > configs;
    configs.resize (pmanager.getNofPartitions(), 0);

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
    unsigned nparts = pmanager.getNofPartitions();

    if (nparts < 2)
    {
        throw OsmtApiException("; Interpolation requires at least 2 partitions.");
    }

    if (nparts == 2)
    {
        produceSingleInterpolant (interpolants);
        return true;
    }

    if ( verbose() ) std::cerr << "; Generalized simultaneous abstraction " << '\n';

    // Generate appropriate masks
    std::vector< ipartitions_t > configs;
    configs.resize (nparts, 0);

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
    unsigned npart = pmanager.getNofPartitions();

    if (npart < 2)
    {
        throw OsmtApiException("; Interpolation requires at least 2 partitions.");
    }

    if (npart == 2)
    {
        produceSingleInterpolant (interpolants);
        return true;
    }

    if ( verbose() ) std::cerr << "; State-transition interpolation " << '\n';

    // Generate appropriate masks
    std::vector< ipartitions_t > configs;
    configs.resize ((2 * npart) + 1, 0);

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

void ProofGraph::produceConfigMatrixInterpolants (const std::vector< vec<int> > &configs, vec<PTRef> &interpolants)
{
    if ( verbose() ) std::cerr << "; General interpolation via configuration matrix " << '\n';

    // Generate appropriate masks
    std::vector< ipartitions_t > parts;
    parts.resize (configs.size(), 0);

    // First interpolant is true -> all partitions in B
    for ( unsigned i = 0; i < parts.size(); i++ )
    {
        for (int j = 0; j < configs[i].size(); ++j)
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
    if ( verbose() ) std::cerr << "; Tree interpolation " << '\n';

    // NOTE some configurations might be empty,
    // if the corresponding nodes in the tree are not approximated
    // TODO

    // Generate appropriate masks
    // NOTE partition ids start from 1, parts vector from 0
    // parts[i] contains configuration mask for partition id i+1
    std::vector< ipartitions_t > parts;
    parts.resize (pmanager.getNofPartitions(), 0);

    // Visit the tree in topological order bottom up and compute the configurations
    std::deque<opensmt::InterpolationTree *> q;
    std::set<int> visited;

    q.push_back (it);

    do
    {
        opensmt::InterpolationTree *node = q.front();
        q.pop_front();
        int pid = node->getPartitionId();

        if (visited.find (pid) == visited.end())
        {
            bool children_visited = true;

            // Make sure all children have been visited, otherwise push them in the queue
            for (opensmt::InterpolationTree * tree : node->getChildren()) {
                int cid = tree->getPartitionId();

                if (visited.find (cid) == visited.end())
                {
                    children_visited = false;
                    q.push_back (tree);
                }
            }

            // All children have been visited
            if (children_visited)
            {
                visited.insert (pid);

                // Compute configuration for this node: A should include the node and the subtree rooted in it
                // In practice the mask is the logical or of the children masks plus the current node
                for (opensmt::InterpolationTree * tree : node->getChildren()) {
                    int cid = tree->getPartitionId();
                    opensmt::orbit(parts[pid - 1], parts[pid - 1], parts[cid - 1]);
                }

                setbit ( parts[pid - 1], pid );
            }
            else
            {
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

bool ProofGraph::producePathInterpolants ( vec<PTRef> &interpolants, const std::vector<ipartitions_t> &A_masks){
    bool propertySatisfied = true;
    // check that masks are subset of each other
#ifndef NDEBUG
    for (int i = 0; i < static_cast<int>(A_masks.size()-1); ++i) {
        assert((A_masks[i] & A_masks[i+1]) == A_masks[i]);
    }
#endif // NDEBUG
    for (int i = 0; i < static_cast<int>(A_masks.size()); ++i) {
        produceSingleInterpolant(interpolants, A_masks[i]);
        if(i > 0 && enabledInterpVerif()){
            PTRef previous_itp = interpolants[interpolants.size() - 2];
            PTRef next_itp = interpolants[interpolants.size() -1];
            PTRef movedPartitions = logic_.mkAnd(pmanager.getPartitions(A_masks[i] ^ A_masks[i-1]));
            propertySatisfied &= VerificationUtils(config, logic_).impliesExternal(logic_.mkAnd(previous_itp, movedPartitions), next_itp);
            if (!propertySatisfied){
                std::cerr << "; Path interpolation does not hold for:\n"
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
    if ( verbose() ) std::cerr << "; Single interpolant " << '\n';

    // Check
    checkInterAlgo();

    // Track AB class variables and associate index to them in nodes bit masks
    computeABVariablesMapping ( A_mask );

    // NOTE generation of interpolants in CNF
    if ( interpolantInCNF() )
    {

        if ( usingMcMillanInterpolation() )
        {
            if ( verbose() > 0 ) std::cerr << "; Proof transformation for interpolants (partially) in CNF" << '\n';

            fillProofGraph();
            proofTransformAndRestructure (-1, -1, true, [this](RuleContext & ra1, RuleContext & ra2 )
                { return this->handleRuleApplicationForCNFinterpolant(ra1, ra2); });
            checkProof (true);
            // Normalize antecedents order ( for interpolation )
            normalizeAntecedentOrder();
            emptyProofGraph();
            printRuleApplicationStatus();
        }
        else
        {
            std::cerr << "; Warning!\n" << "; Please set McMillan interpolation algorithm to generate interpolants in CNF";
        }


    }
    // NOTE Preliminary application of A2 rules to strengthen/weaken the interpolant
    // Not compatible with interpolants in CNF
    //else if( restructuringForStrongerInterpolant() || restructuringForWeakerInterpolant() )
    // TODO enable proof reduction
    else if (0)
    {
        if ( verbose() > 0 && restructuringForStrongerInterpolant() ) std::cerr << "; Preliminary A2 rules application to strengthen interpolants" << '\n';

        if ( verbose() > 0 && restructuringForWeakerInterpolant() ) std::cerr << "; Preliminary A2 rules application to weaken interpolants" << '\n';

        fillProofGraph();
        // NOTE Only a couple of loops to avoid too much overhead
        proofTransformAndRestructure (-1, 2, true, [this] (RuleContext & ra1, RuleContext & ra2) {
            return this->handleRuleApplicationForStrongerWeakerInterpolant(ra1, ra2);
        });
        // Normalize antecedents order ( for interpolation )
        normalizeAntecedentOrder();
        emptyProofGraph();
    }

    // Clause and partial interpolant
    ProofNode *n = nullptr;
    PTRef partial_interp = PTRef_Undef;

    // Vector for topological ordering
    std::vector< clauseid_t > DFSv;
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
            if (!isLeafClauseType(n->getType())) throw OsmtInternalException("; Leaf node with non-leaf clause type");

            std::vector<Lit> &cl = n->getClause();
            bool fal = false;

            if (cl.size() == 0) {
                assert(false);
                throw OsmtInternalException("; Empty clause found in interpolation\n");
            }
            Logic &logic = this->logic_;
            if (cl.size() == 1 && varToPTRef(var(cl[0])) == logic.getTerm_false() && !sign(cl[0])) {
                fal = true;
            }

            if ((n->getType() == clause_type::CLA_ORIG && n->getClauseRef() == CRef_Undef) || fal)
            {
                //unit clause False exists, return degenerate interpolant
                icolor_t cc = getClauseColor (n->getInterpPartitionMask(), A_mask);
                interpolants.push( cc == icolor_t::I_A ? logic.getTerm_false() : logic.getTerm_true());

                if (verbose()) {
                    std::cout << "; Degenerate interpolant" << std::endl;
                }
                return;
            }
        }
    }

    if (verbose() > 0) std::cerr << "; Generating interpolant " << std::endl;

    std::map<Var, icolor_t> *PSFunction = computePSFunction (DFSv, A_mask);

    // Traverse proof and compute current interpolant
    for ( size_t i = 0 ; i < proof_size ; i++ )
    {
        n = getNode ( DFSv[ i ] );
        assert (n);

        // Generate partial interpolant for clause i
        if (n->isLeaf())
        {
            if (!isLeafClauseType(n->getType())) throw OsmtInternalException("; Leaf node with non-leaf clause type");

            labelLeaf (n, 0, PSFunction);

            if (n->getType() == clause_type::CLA_ORIG)
            {
                partial_interp = compInterpLabelingOriginal(n, A_mask);
            }
            else if (n->getType() == clause_type::CLA_THEORY) // Theory lemma
            {
                clearTSolver();
                vec<Lit> newvec;
                std::vector<Lit> &oldvec = n->getClause();

                for (std::size_t j = 0; j < oldvec.size(); ++j) {
                    newvec.push(~oldvec[j]);
                }

#ifdef ITP_DEBUG
                std::cout << "; ASSERTING LITS" << '\n';
                vec<PTRef> tr_vec;
                Logic& logic = thandler->getLogic();
                for (int i = 0; i < newvec.size(); ++i) {
                    PTRef tr_vecel = thandler->varToTerm(var(newvec[i]));
                    tr_vec.push(sign(newvec[i]) ? logic.mkNot(tr_vecel) : tr_vecel);
                }
                PTRef tr_and = logic.mkAnd(tr_vec);
                printf("%s\n", logic.printTerm(tr_and));
#endif
                bool res = this->assertLiteralsToTSolver(newvec);
                if (res) {
                    TRes tres = thandler->check(true);
                    res = (tres != TRes::UNSAT);
                }
                assert(!res);
                std::map<PTRef, icolor_t> ptref2label;
                std::vector<Lit>& cl = n->getClause();

                for (std::size_t j = 0; j < cl.size(); ++j) {
                    ptref2label[varToPTRef(var(cl[j]))] = getVarColor(n, var(cl[j]));
                }

                partial_interp = thandler->getInterpolant (A_mask, &ptref2label, pmanager);
                clearTSolver();
            }
            else if (n->getType() == clause_type::CLA_SPLIT) {
                auto const & clause = n->getClause();
                assert(clause.size() == 2); // only binary splits at the moment
                auto color = getVarColor(n, var(clause[0]));
                assert(color == getVarColor(n, var(clause[1]))); // same theory variables in the atoms of the split => same color
                assert(color == icolor_t::I_A || color == icolor_t::I_B || color == icolor_t::I_AB);
                // If split on A-local (B-local) term, then return False (True). This is the same as in purely propoositional case.
                // If split on AB-shared term, we can choose if we treat it as A-clause (resulting in False) or B-clause (resulting in True). We arbitrarily choose A now.
                partial_interp = color == icolor_t::I_A ? logic_.getTerm_false() : (color == icolor_t::I_B ? logic_.getTerm_true() : logic_.getTerm_false());
            }
            else {
                assert(n->getType() == clause_type::CLA_ASSUMPTION);
                // MB: Frame literals must be ignored when interpolating
                // This interpolant will be ignored eventually, any value would do
                n->setPartialInterpolant (logic_.getTerm_true());
                continue;
            }

            assert ( partial_interp != PTRef_Undef );
            n->setPartialInterpolant ( partial_interp );
            if (enabledPedInterpVerif()) {
                verifyPartialInterpolant(n, A_mask);
            }
        }
        else
        {
            partial_interp = compInterpLabelingInner ( n );
            assert ( partial_interp != PTRef_Undef );
            n->setPartialInterpolant ( partial_interp );
        }
    }

    delete PSFunction;

    // Last clause visited is the empty clause with total interpolant
    assert (partial_interp == getRoot()->getPartialInterpolant());

    if( verbose() )
    {
        //getComplexityInterpolant(partial_interp);
        
        int nbool, neq, nuf, nif;
        this->logic_.collectStats(partial_interp, nbool, neq, nuf, nif);
        std::cerr << "; Number of boolean connectives: " << nbool << '\n';
        std::cerr << "; Number of equalities: " << neq << '\n';
        std::cerr << "; Number of uninterpreted functions: " << nuf << '\n';
        std::cerr << "; Number of interpreted functions: " << nif << '\n';
        
    }

    //if ( enabledInterpVerif() ) verifyPartialInterpolantFromLeaves( getRoot(), A_mask );
    if ( enabledInterpVerif() )
    {
        PTRef partA = pmanager.getPartition(A_mask, PartitionManager::part::A);
        PTRef partB = pmanager.getPartition(A_mask, PartitionManager::part::B);
        bool sound = VerificationUtils(config, logic_).verifyInterpolantExternal(partA, partB, getRoot()->getPartialInterpolant());

        if(verbose())
        {
            if (sound) std::cout << "; Final interpolant is sound" << '\n';
            else std::cout << "; Final interpolant is NOT sound" << '\n';
        }
    }

    PTRef interpol = getRoot()->getPartialInterpolant();
    assert (interpol != PTRef_Undef);

    const bool cannotSimplify = !(logic_.isBooleanOperator(interpol) && !logic_.isNot(interpol));

    if (!cannotSimplify) {
        if(simplifyInterpolant() == 4) {
            interpol = ::rewriteMaxArityAggresive(logic_, interpol);
            interpol = ::simplifyUnderAssignment_Aggressive(interpol, logic_);
        }
        else {
            if (simplifyInterpolant() > 0) {
                if (verbose() > 1) {
                    std::cout << "Itp before rewriting max arity: \n" << logic_.printTerm(interpol) << "\n\n";
                }
                interpol = ::rewriteMaxArityClassic(logic_, interpol);
            }
            if (simplifyInterpolant() == 2) {
                if (verbose() > 1) {
                    std::cout << "Itp before aggressive simplifying: \n" << logic_.printTerm(interpol) << "\n\n";
                }
                interpol = ::simplifyUnderAssignment(logic_, interpol);
            }

            if (simplifyInterpolant() == 3) {
                if (verbose() > 1) {
                    std::cout << "Itp before aggressive simplifying: \n" << logic_.printTerm(interpol) << "\n\n";
                }
                interpol = ::simplifyUnderAssignment_Aggressive(interpol, logic_);
            }
        }
    }

    interpolants.push ( interpol );

    if(verbose() > 1)
    {
        std::cout << "; Interpolant:\n" << this->logic_.printTerm(interpol) << '\n';
    }
}

void ProofGraph::produceMultipleInterpolants ( const std::vector< ipartitions_t > &configs, vec<PTRef> &sequence_of_interpolants )
{
    // Check
    checkInterAlgo();

    if ( needProofStatistics() )
    {
    }

    assert ( sequence_of_interpolants.size( ) == 0 );

    // Clause and partial interpolant
    ProofNode *n;
    PTRef partial_interp;

    // Vector for topological ordering
    std::vector< clauseid_t > DFSv;
    // Compute topological sorting of graph
    topolSortingTopDown ( DFSv );
    size_t proof_size = DFSv.size();

    // Degenerate proof
    if (proof_size == 1) throw OsmtInternalException("Degenerate proof, only empty clause - Cannot calculate interpolants");

    for ( unsigned curr_interp = 0; curr_interp < configs.size(); curr_interp ++ )
    {
        if ( verbose() > 0 ) std::cerr << "# Generating interpolant " << curr_interp << '\n';

        const ipartitions_t &A_mask = configs[curr_interp];

        // Track AB class variables and associate index to them in nodes bit masks
        computeABVariablesMapping ( A_mask );

        std::map<Var, icolor_t> *PSFunction = computePSFunction (DFSv, A_mask);

        // Traverse proof and compute current interpolant
        for ( size_t i = 0 ; i < proof_size ; i++ )
        {
            n = getNode ( DFSv[ i ] );
            assert (n);

            // Generate partial interpolant for clause i
            if (n->isLeaf())
            {
                // FIXME: This check is outdated
                if (n->getType() != clause_type::CLA_ORIG) throw OsmtInternalException ( "Leaf clause is not original" );

                partial_interp = compInterpLabelingOriginal(n, A_mask);
                //if ( enabledPedInterpVerif() ) verifyPartialInterpolantFromLeaves( n, A_mask );

            }
            else
            {
                partial_interp = compInterpLabelingInner ( n );
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

        if ( printProofDotty( ) == 1 )
        {
            char buf[ 32 ];
            sprintf ( buf, "proof_interp_%d.dot", curr_interp );
            std::ofstream dotty ( buf );
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
        throw OsmtApiException("Incorrect interpolation algorithm set for labeling-based interpolation");

    icolor_t clause_color = getClauseColor ( n->getInterpPartitionMask(), A_mask );
    // Original leaves can be only of class A or B
    assert ( clause_color == icolor_t::I_A || clause_color == icolor_t::I_B );

    PTRef partial_interp = PTRef_Undef;

    // Leaf belongs to A
    if ( clause_color == icolor_t::I_A )
    {
        // McMillan: compute clause restricted to AB
        if ( usingMcMillanInterpolation( ) )
        {
            std::vector< Lit > restricted_clause;
            icolor_t var_class;
            std::vector< Lit > &cl = n->getClause();
            const size_t size = cl.size( );

            for ( size_t i = 0 ; i < size ; i ++ )
            {
                var_class = getVarClass ( var (cl[i]), A_mask );

                if ( var_class == icolor_t::I_AB ) restricted_clause.push_back ( cl[i] );
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

                partial_interp = logic_.mkOr (std::move(or_args));
                assert (partial_interp != PTRef_Undef);
            }
        }
        // Pudlak or McMillan': false
        else
        {
            partial_interp = logic_.getTerm_false(); //logic_.mkFalse( );
        }
    }
    // Leaf belongs to B
    else if ( clause_color == icolor_t::I_B )
    {
        //  McMillan': compute clause restricted to a
        if ( usingMcMillanPrimeInterpolation( ) )
        {
            std::vector< Lit > restricted_clause;
            icolor_t var_class;
            std::vector< Lit > &cl = n->getClause();
            const size_t size = cl.size( );

            for ( size_t i = 0 ; i < size ; i ++ )
            {
                var_class = getVarClass ( var (cl[i]), A_mask );

                if ( var_class == icolor_t::I_AB ) restricted_clause.push_back ( cl[i] );
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

                partial_interp = logic_.mkAnd (std::move(and_args));
                assert (partial_interp != PTRef_Undef);
            }
        }
        // Pudlak or McMillan': true
        else
        {
            partial_interp = logic_.getTerm_true();
        }
    }
    else throw OsmtInternalException("Clause has no color" );

    return partial_interp;
}

// Input: inner clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
PTRef ProofGraph::compInterpLabelingInnerSimple ( ProofNode *n, const ipartitions_t &A_mask )
{
    if (! ( usingMcMillanInterpolation( ) || usingPudlakInterpolation( ) || usingMcMillanPrimeInterpolation( ) ) )
        throw OsmtApiException("Incorrect interpolation algorithm set for labeling-based interpolation");

    // Get antecedents partial interpolants
    PTRef partial_interp_ant1 = n->getAnt1()->getPartialInterpolant();
    PTRef partial_interp_ant2 = n->getAnt2()->getPartialInterpolant();
    assert ( partial_interp_ant1 != PTRef_Undef );
    assert ( partial_interp_ant2 != PTRef_Undef );

    PTRef partial_interp = PTRef_Undef;
    // Determine class pivot
    icolor_t pivot_class = getVarClass ( n->getPivot(), A_mask );

    // Pivot class A -> interpolant = interpolant of ant1 OR interpolant of ant2
    if ( pivot_class == icolor_t::I_A )
    {
        partial_interp = logic_.mkOr({partial_interp_ant1, partial_interp_ant2});
        assert (partial_interp != PTRef_Undef);
    }
    // Pivot class B -> interpolant = interpolant of ant1 AND interpolant of ant2
    else if ( pivot_class == icolor_t::I_B )
    {
        partial_interp = logic_.mkAnd({partial_interp_ant1, partial_interp_ant2});
        assert (partial_interp != PTRef_Undef);
    }
    // Pivot class AB ->
    // 1) Pudlak interpolant = (pivot OR interpolant of ant1) AND ((NOT pivot) OR interpolant of ant2)
    // 1) Alternative interpolant = ((NOT pivot) AND interpolant of ant1) OR (pivot AND interpolant of ant2)
    // 2) McMillan interpolant  = interpolant of ant1 AND interpolant of ant2
    // 3) McMillan' interpolant = interpolant of ant1 OR interpolant of ant2
    else if ( pivot_class == icolor_t::I_AB)
    {
        if ( usingPudlakInterpolation( ) )
        {
            // Find pivot occurrences in ant1 and ant2 and create enodes
            Var piv_ = n->getPivot();
            PTRef piv = varToPTRef ( piv_ );
            bool choose_alternative = false;

            if ( usingAlternativeInterpolant() ) choose_alternative = decideOnAlternativeInterpolation ( n );

            // Equivalent formula (I_1 /\ ~p) \/ (I_2 /\ p)
            if ( choose_alternative )
            {
                PTRef and_1 = logic_.mkAnd({partial_interp_ant1, logic_.mkNot(piv)});
                PTRef and_2 = logic_.mkAnd({partial_interp_ant2, piv});
                partial_interp = logic_.mkOr({and_1, and_2});

//              PTRef and_1 = logic_.mkAnd( logic_.cons( partial_interp_ant1, logic_.cons( logic_.mkNot( logic_.cons( piv ) ) ) ) );
//              PTRef and_2 = logic_.mkAnd( logic_.cons( partial_interp_ant2, logic_.cons( piv ) ) );
//              partial_interp = logic_.mkOr( logic_.cons( and_1, logic_.cons( and_2 ) ) );
                // TODO ~piv \/ piv is not simplified, but should be!
                assert (partial_interp != logic_.getTerm_true());
                assert (partial_interp != PTRef_Undef);
            }
            // Standard interpolation (I_1 \/ p) /\ (I_2 \/ ~p)
            else
            {
                PTRef or_1 = logic_.mkOr({partial_interp_ant1, piv});
                PTRef or_2 = logic_.mkOr({partial_interp_ant2, logic_.mkNot(piv)});
                partial_interp = logic_.mkAnd({or_1, or_2});

//              PTRef or_1 = logic_.mkOr( logic_.cons( partial_interp_ant1, logic_.cons( piv ) ) );
//              PTRef or_2 = logic_.mkOr( logic_.cons( partial_interp_ant2, logic_.cons( logic_.mkNot( logic_.cons( piv ) ) ) ) );
//              partial_interp = logic_.mkAnd( logic_.cons( or_1, logic_.cons( or_2 ) ) );
                // TODO piv /\ ~piv is not simplified, but should be!
                assert (partial_interp != logic_.getTerm_false());
                assert (partial_interp != PTRef_Undef);
            }
        }
        else if ( usingMcMillanInterpolation( ) )
        {
            partial_interp = logic_.mkAnd({partial_interp_ant1, partial_interp_ant2});
            assert (partial_interp != PTRef_Undef);
        }
        else if ( usingMcMillanPrimeInterpolation( ) )
        {
            partial_interp = logic_.mkOr({partial_interp_ant1, partial_interp_ant2});
            assert (partial_interp != PTRef_Undef);
        }
        else throw OsmtApiException("No interpolation algorithm");
    }
    else throw OsmtInternalException("Pivot has no class");

    return partial_interp;
}

void ProofGraph::checkInterAlgo()
{
    if ( ! ( usingMcMillanInterpolation()
             || usingPudlakInterpolation()
             || usingMcMillanPrimeInterpolation()
             || usingPSInterpolation()
             || usingPSWInterpolation()
             || usingPSSInterpolation()
             || usingLabelingSuggestions()))
        throw OsmtApiException("Please choose 0/1/2/3/4/5/6 as values for itp_bool_algo");

    if ( verbose() > 0 )
    {
        std::cerr << "# Using ";

        if ( usingPudlakInterpolation() )
            std::cerr << "Pudlak";
        else if ( usingMcMillanInterpolation() )
            std::cerr << "McMillan";
        else if ( usingMcMillanPrimeInterpolation() )
            std::cerr << "McMillan'";
        else if (  usingPSInterpolation() )
            std::cerr << "Proof-Sensitive";
        else if (  usingPSWInterpolation() )
            std::cerr << "Weak Proof-Sensitive";
        else if (  usingPSSInterpolation() )
            std::cerr << "Strong Proof-Sensitive";
        else if ( usingLabelingSuggestions() )
            std::cerr << "labeling suggestions";

        std::cerr << " for propositional interpolation" << '\n';
    }
}


/********** FULL LABELING BASED INTERPOLATION **********/



void
ProofGraph::labelLeaf(ProofNode * n, unsigned num_config, std::map<Var, icolor_t> * PSFunction)
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
    else throw OsmtApiException("No interpolation algorithm chosen");
}

// Input: leaf clause, current interpolant partition masks for A and B
// Output: Labeling-based partial interpolant for the clause
PTRef ProofGraph::compInterpLabelingOriginal(ProofNode * n, const ipartitions_t & A_mask)
{
    // Then calculate interpolant
    icolor_t clause_color = getClauseColor ( n->getInterpPartitionMask(), A_mask );
#ifdef ITP_DEBUG
    std::cout << "Clause has mask " << n->getInterpPartitionMask() << ". Mask " << A_mask << '\n';
    std::cout << "Clause has color " << clause_color << '\n';
#endif

    if (clause_color == icolor_t::I_AB)
    {
        // Think of a heuristic for choosing the partition?
        clause_color = icolor_t::I_A;
    }

    // Original leaves can be only of class A or B
    assert ( clause_color == icolor_t::I_A || clause_color == icolor_t::I_B );

    PTRef partial_interp = PTRef_Undef;

    // MB: TODO unite the cases in one function
    // Leaf belongs to A -> interpolant = leaf clause restricted to b
    if ( clause_color == icolor_t::I_A )
    {
        //Compute clause restricted to b

        std::vector< Lit > restricted_clause;
        // In labeling, classes and colors are distinct
        icolor_t var_class;
        icolor_t var_color;
        std::vector< Lit > &cl = n->getClause();

        const size_t size = cl.size( );

        for ( size_t i = 0 ; i < size ; i ++ )
        {
            if (isAssumedLiteral(~cl[i])) {
                // ignore if the negation is assumed, it's as if this literal did not exist
                continue;
            }
            Var v = var (cl[i]);
            var_class = getVarClass2 ( v );
            assert ( var_class == icolor_t::I_B || var_class == icolor_t::I_A || var_class == icolor_t::I_AB );

            if ( var_class == icolor_t::I_B || var_class == icolor_t::I_A ) var_color = var_class;
            else
            {
                // Determine color of AB variable
                if ( isColoredA ( n, v ) ) var_color = icolor_t::I_A;
                else if ( isColoredB ( n, v )  ) var_color = icolor_t::I_B;
                else if ( isColoredAB ( n, v ) ) var_color = icolor_t::I_AB;
                else throw OsmtInternalException("Variable " + std::to_string(v) + " has no color in clause " + std::to_string(n->getId()));
            }

            if ( var_color == icolor_t::I_B ) restricted_clause.push_back ( cl[i] );
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
                if (sign (restricted_clause[i])) lit = logic_.mkNot(lit);

                //Build adding literals progressively
                or_args.push (lit);
            }
            partial_interp = logic_.mkOr(std::move(or_args));
        }
    }
    // Leaf belongs to B -> interpolant = negation of leaf clause restricted to a
    else if ( clause_color == icolor_t::I_B )
    {
        //Compute clause restricted to a

        std::vector< Lit > restricted_clause;
        // In labeling, classes and colors are distinct
        icolor_t var_class;
        icolor_t var_color;
        std::vector< Lit > &cl = n->getClause();

        const size_t size = cl.size( );

        for ( size_t i = 0 ; i < size ; i ++ )
        {
            if (isAssumedLiteral(~cl[i])) {
                // ignore if the negation is assumed, it's as if this literal did not exist
                continue;
            }
            Var v = var (cl[i]);
            var_class = getVarClass2 ( v );
            assert ( var_class == icolor_t::I_B || var_class == icolor_t::I_A || var_class == icolor_t::I_AB );

            if ( var_class == icolor_t::I_B || var_class == icolor_t::I_A ) var_color = var_class;
            else
            {
                // Determine color of AB variable
                if ( isColoredA ( n, v ) ) var_color = icolor_t::I_A;
                else if ( isColoredB ( n, v )  ) var_color = icolor_t::I_B;
                else if ( isColoredAB ( n, v ) ) var_color = icolor_t::I_AB;
                else throw OsmtInternalException("Variable " + std::to_string(v) + " has no color in clause " + std::to_string(n->getId()));
            }

            if ( var_color == icolor_t::I_A ) restricted_clause.push_back ( cl[i] );
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
                    lit = logic_.mkNot(lit);

                // Build adding literals progressively
                and_args.push (lit);
            }
            partial_interp = logic_.mkAnd (std::move(and_args));
        }
    }
    else throw OsmtInternalException("Clause has no color");

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
    if (pivot_color == icolor_t::I_S) {
        Var v = n->getPivot();
        Lit pos = mkLit(v);
        if(isAssumedLiteral(pos)) {
            // Positive occurence is in first parent
            // Retuen interpolant from second
            return partial_interp_ant2;
        }
        else {
            assert(isAssumedLiteral(~pos));
            return partial_interp_ant1;
        }
    }

    // Pivot colored a -> interpolant = interpolant of ant1 OR interpolant of ant2
    if ( pivot_color == icolor_t::I_A)
    {
        partial_interp = logic_.mkOr({partial_interp_ant1, partial_interp_ant2});
    }
    // Pivot colored b -> interpolant = interpolant of ant1 AND interpolant of ant2
    else if ( pivot_color == icolor_t::I_B )
    {
        partial_interp = logic_.mkAnd({partial_interp_ant1, partial_interp_ant2});
    }
    // Pivot colored ab -> interpolant = (pivot OR interpolant of ant1) AND ((NOT pivot) OR interpolant of ant2)
    // Alternative interpolant = ((NOT pivot) AND interpolant of ant1) OR (pivot AND interpolant of ant2)
    else if ( pivot_color == icolor_t::I_AB)
    {
        // Find pivot occurrences in ant1 and ant2 and create enodes
        Var piv_ = n->getPivot();
        PTRef piv = varToPTRef ( piv_ );
        bool choose_alternative = false;

        if ( usingAlternativeInterpolant() ) choose_alternative = decideOnAlternativeInterpolation ( n );

        // Equivalent formula (I_1 /\ ~p) \/ (I_2 /\ p)
        if ( choose_alternative )
        {
            PTRef and_1 = logic_.mkAnd({partial_interp_ant1, logic_.mkNot(piv)});
            PTRef and_2 = logic_.mkAnd({partial_interp_ant2, piv});

            if (logic_.isNot (and_1) && (logic_.getPterm (and_1)[0] == and_2))
                partial_interp = logic_.getTerm_true();
            else if (logic_.isNot (and_2) && (logic_.getPterm (and_2)[0] == and_1))
                partial_interp = logic_.getTerm_true();
            else
            {
                partial_interp = logic_.mkOr({and_1, and_2});
                assert (partial_interp != logic_.getTerm_true());
            }
        }
        // Standard interpolation (I_1 \/ p) /\ (I_2 \/ ~p)
        else
        {
            PTRef or_1 = logic_.mkOr({partial_interp_ant1, piv});
            PTRef or_2 = logic_.mkOr({partial_interp_ant2, logic_.mkNot(piv)});

            if (logic_.isNot (or_1) && (logic_.getPterm (or_1)[0] == or_2))
                partial_interp = logic_.getTerm_false();
            else if (logic_.isNot (or_2) && (logic_.getPterm (or_2)[0] == or_1))
                partial_interp = logic_.getTerm_false();
            else
            {
                partial_interp = logic_.mkAnd({or_1, or_2});
                assert (partial_interp != logic_.getTerm_false());
            }

        }
    }
    else throw OsmtInternalException("Pivot has no color");

    return partial_interp;
}

void
ProofGraph::setLeafPSLabeling (ProofNode *n, std::map<Var, icolor_t> *labels)
{
    assert (labels != NULL);
    //Reset labeling
    resetLabeling (n);

    std::vector<Lit> &cl = n->getClause();

    for (unsigned i = 0; i < cl.size(); ++i)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 (v);

        // Color AB class variables based on the map "labels"
        if (var_class == icolor_t::I_AB)
        {
            auto it = labels->find(v);
            assert (theory_only.find(v) != theory_only.end() || it != labels->end());

            if (it->second == icolor_t::I_A)
                colorA (n, v);
            else
                colorB (n, v);
        }
        else if (var_class == icolor_t::I_A || var_class == icolor_t::I_B);
        else throw OsmtInternalException("Variable has no class");
    }
}

void
ProofGraph::setLeafPSWLabeling (ProofNode *n, std::map<Var, icolor_t> *labels)
{
    assert (labels != NULL);
    //Reset labeling
    resetLabeling (n);

    std::vector<Lit> &cl = n->getClause();

    for (unsigned i = 0; i < cl.size(); ++i)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 (v);

        // Color AB class variables based on the map "labels"
        if (var_class == icolor_t::I_AB)
        {
            auto it = labels->find (v);
            assert (theory_only.find(v) != theory_only.end() || it != labels->end());

            if (it->second == icolor_t::I_A)
                colorA (n, v);
            else
                colorAB (n, v);
        }
        else if (var_class == icolor_t::I_A || var_class == icolor_t::I_B);
        else throw OsmtInternalException("Variable has no class");
    }
}

void
ProofGraph::setLeafPSSLabeling (ProofNode *n, std::map<Var, icolor_t> *labels)
{
    assert (labels != NULL);
    //Reset labeling
    resetLabeling (n);

    std::vector<Lit> &cl = n->getClause();

    for (unsigned i = 0; i < cl.size(); ++i)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 (v);

        // Color AB class variables based on the map "labels"
        if (var_class == icolor_t::I_AB)
        {
            auto it = labels->find(v);
            assert (theory_only.find(v) != theory_only.end() || it != labels->end());

            if (it->second == icolor_t::I_A)
                colorAB (n, v);
            else
                colorB (n, v);
        }
        else if (var_class == icolor_t::I_A || var_class == icolor_t::I_B);
        else throw OsmtInternalException("Variable has no class");
    }
}
void ProofGraph::setLeafPudlakLabeling ( ProofNode *n )
{
    // Reset labeling
    resetLabeling ( n );

    std::vector< Lit > &cl = n->getClause();

    for ( unsigned i = 0; i < cl.size(); i++)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 ( v );

        // Color AB class variables as ab
        if ( var_class == icolor_t::I_AB ) colorAB (n, v);
        else if ( var_class == icolor_t::I_A || var_class == icolor_t::I_B );
        else throw OsmtInternalException("Variable has no class");
    }
}

void ProofGraph::setLeafMcMillanLabeling ( ProofNode *n )
{
    // Reset labeling
    resetLabeling (n);
    std::vector< Lit > &cl = n->getClause();

    for ( unsigned i = 0; i < cl.size(); i++)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 ( v );

        // Color AB class variables as b
        if ( var_class == icolor_t::I_AB ) colorB (n, v);
        else if ( var_class == icolor_t::I_A || var_class == icolor_t::I_B );
        else throw OsmtInternalException("Variable has no class");
    }
}

void ProofGraph::setLeafMcMillanPrimeLabeling ( ProofNode *n )
{
    // Reset labeling
    resetLabeling (n);

    std::vector< Lit > &cl = n->getClause();

    for ( unsigned i = 0; i < cl.size(); i++)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 ( v );

        // Color AB class variables a if clause is in A
        if ( var_class == icolor_t::I_AB ) colorA (n, v);
        // Color AB class variables b if clause is in B
        else if ( var_class == icolor_t::I_A || var_class == icolor_t::I_B );
        else throw OsmtInternalException("Variable has no class");
    }
}

void ProofGraph::setLabelingFromMap ( ProofNode *n, unsigned num_config )
{
    assert (vars_suggested_color_map);
    // Reset labeling
    resetLabeling (n);

    std::vector< Lit > &cl = n->getClause();

    for ( unsigned i = 0; i < cl.size(); i++)
    {
        Var v = var (cl[i]);
        icolor_t var_class = getVarClass2 ( v );

        // Color AB class variables as a
        if ( var_class == icolor_t::I_AB )
        {
            // Retrieve correspondent Enode
            PTRef en = varToPTRef (v);
            std::map<PTRef, icolor_t> *col_map = (*vars_suggested_color_map)[num_config];
            assert (col_map);
            std::map<PTRef, icolor_t>::iterator it = col_map->find (en);

            if ( it == col_map->end() )
            {
                std::cerr << "Color suggestion for " << v << " not found; using Pudlak" << '\n';
                colorAB (n, v);
            }
            else
            {
                icolor_t color = it->second;

                if (color == icolor_t::I_A) colorA (n, v);
                else if (color == icolor_t::I_B) colorB (n, v);
                else if (color == icolor_t::I_AB) colorAB (n, v);
                else throw OsmtInternalException("Variable " + std::to_string(v) + " has no color in clause " + std::to_string(n->getId()));
            }
        }
        else if ( var_class == icolor_t::I_A || var_class == icolor_t::I_B );
        else throw OsmtInternalException("Variable has no class");
    }
}

icolor_t ProofGraph::getVarClass2(Var v) {
    int c = getVarInfoFromMapping(v); assert(c>=-2);
    return c == -1 ? icolor_t::I_A : (c == -2 ? icolor_t::I_B : icolor_t::I_AB);
}

// HELPER methods for theory solver
void ProofGraph::clearTSolver() {
    thandler->backtrack(-1);
}

bool ProofGraph::assertLiteralsToTSolver(vec<Lit> const & vec) {
    return thandler->assertLits(vec);
}


