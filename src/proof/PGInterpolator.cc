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

#include <deque>
#include <iostream>

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
    if (verbose()) std::cerr << "; Single interpolant " << '\n';

    // Check
    checkInterAlgo();

    // Track AB class variables and associate index to them in nodes bit masks
    computeABVariablesMapping(A_mask);

    // Clause and partial interpolant
    ProofNode *n = nullptr;
    PTRef partial_interp = PTRef_Undef;

    // Vector for topological ordering
    std::vector< clauseid_t > DFSv;
    // Compute topological sorting of graph
    topolSortingTopDown ( DFSv );
    size_t proof_size = DFSv.size();

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


