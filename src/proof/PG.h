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

#ifndef PROOFGRAPH_H
#define PROOFGRAPH_H

#include "InterpolationUtils.h"
#include "Proof.h"
#include "PTRef.h"
#include "Theory.h"
#include "THandler.h"
#include "PartitionManager.h"
#include "OsmtInternalException.h"

#include <memory>
#include <map>
#include <new>
#include <functional>

using namespace opensmt;

class Proof;
class Logic;
struct SMTConfig;

typedef unsigned clauseid_t;

// Types of rules
enum rul_type
{
	rA1
	, rA2
	, rA2u
	, rB2
	, rB3
	, rB1
	, rB2prime
	, rA1B
	, rA2B
	, rA1prime
	, rNO
};

inline bool isSwapRule (rul_type rt)  { return rt==rA1 || rt==rA1B || rt==rA1prime || rt==rA2 || rt==rA2B || rt==rA2u || rt==rB2; }
inline bool isCutRule  (rul_type rt)  { return rt==rB1 || rt==rB2prime || rt==rB3; }

// Rules applicability info
// Five nodes context plus type of applicable rule
class RuleContext
{
public:
	RuleContext ( )
: type( rNO )
, cv1 ( -1 )
, cv2 ( -1 )
, cw  ( -1 )
, cv3 ( -1 )
, cv  ( -1 )
{ }

	~RuleContext ( ) { }

	inline void reset( )
	{
		type = rNO;
		cv1 = -1;
		cv2 = -1;
		cw = -1;
		cv3 = -1;
		cv = -1;
	}

	inline bool enabled() const { return (type!=rNO); }
	inline bool disabled() const { return (type==rNO); }
	inline rul_type getType() const { return type; }

	inline clauseid_t getW() const { return cw; }
	inline clauseid_t getV1() const { return cv1; }
	inline clauseid_t getV2() const { return cv2; }
	inline clauseid_t getV3() const { return cv3; }
	inline clauseid_t getV() const { return cv; }

	rul_type   type;
	clauseid_t cv1;
	clauseid_t cv2;
	clauseid_t cw;
	clauseid_t cv3;
	clauseid_t cv;

	friend std::ostream& operator<< (std::ostream &out, RuleContext &ra);
};

// Resolution proof graph element
struct ProofNode
{
    ProofNode    ()
    : clause     (nullptr)
    , clause_ref (CRef_Undef)
    , pivot      (-1)
    , ant1       (nullptr)
    , ant2       (nullptr)
    , resolvents ()
    { }

    ~ProofNode ( )
    {
        delete clause;
    }

    //
    // Auxiliary
    //
    inline void                 resetClause() { delete clause; clause = NULL; }

    void setClauseRef(CRef cref)
    {
        clause_ref = cref;
    }
    CRef getClauseRef() const { return clause_ref; }

    void                        initClause(Clause& cla)
    {
        assert(clause == NULL);
        clause = new std::vector<Lit>(cla.size());
        for(size_t k = 0; k < cla.size(); ++k) (*clause)[k] = cla[k];
    }

    void                        initClause(std::vector<Lit>& cla)
    {
        assert(clause == NULL);
        clause = new std::vector<Lit>(cla.size());
        for(size_t k = 0; k < cla.size(); ++k) (*clause)[k] = cla[k];
    }

    void                        setClause(std::vector<Lit>& cla)
    {
        assert(clause);
        clause->resize(cla.size());
        for(size_t k = 0; k < cla.size(); ++k) (*clause)[k] = cla[k];
    }

    void initClause()
    {
        assert(clause == NULL);
        clause = new std::vector<Lit>;
    }

    //
    // Getty methods
    //
    inline clauseid_t            getId                  ( ) const { return id; }
    inline std::vector<Lit> &         getClause              ( )       { assert(clause); return *clause; }
    inline std::vector<Lit> const &   getClause              ( ) const { assert(clause); return *clause; }
    inline std::vector<Lit> const *   getPClause             ( ) const { return clause; }
    inline size_t                getClauseSize          ( ) const { return clause->size( ); }
    inline Var                   getPivot               ( ) const { return pivot; }
    inline ProofNode *           getAnt1                ( ) const { return ant1; }
    inline ProofNode *           getAnt2                ( ) const { return ant2; }
    inline clause_type           getType                ( ) const { return type; }
    unsigned                     getNumResolvents       ( ) const { return resolvents.size(); }
    std::set<clauseid_t>&        getResolvents          ( ) { return resolvents; }
    //
    // Setty methods
    //
    inline void                  setId                  ( clauseid_t new_id )            { id = new_id; }
    inline void                  setPivot               ( Var new_pivot )                { pivot = new_pivot; }
    inline void                  setAnt1                ( ProofNode * a1 )               { ant1 = a1; }
    inline void                  setAnt2                ( ProofNode * a2 )               { ant2 = a2; }
    inline void                  setType                ( clause_type new_type )         { type = new_type; }
    void                         addRes                 ( clauseid_t id )                { resolvents.insert( id ); }
    void                         remRes                 ( clauseid_t id )                { resolvents.erase( id ); }
    //
    // Test methods
    //
    inline bool isLeaf() const {
        assert((ant1 and ant2 ) or (not ant1 and not ant2));
        return not ant1;
    }
    // 0 if positive, 1 if negative, -1 if not found
    short                         hasOccurrenceBin( Var );
    // true if positive occurrence pivot is in first antecedent
    bool                          checkPolarityAnt();


private:
    clauseid_t         id;                 // id
    std::vector<Lit>*     clause;             // Clause
    CRef clause_ref;
    Var                pivot;              // Non-leaf node pivot
    ProofNode *        ant1;               // Edges to antecedents
    ProofNode *        ant2;               // Edges to antecedents
    std::set<clauseid_t> resolvents;       // Resolvents
    clause_type        type;               // Node type
};

class InterpolationInfo {
    // Interpolation data for resolution proof element
    struct InterpolationNodeData
    {
        // NOTE labeling rules for AB variables
        // color a:  bit 1, bit 0
        // color b:  bit 0, bit 1
        // color ab: bit 1, bit 1
        // missing:  bit 0, bit 0
        // This notation is consistent with coloring of inner nodes given by | of antecedents colorings
        ipartitions_t      AB_vars_a_colored;
        ipartitions_t      AB_vars_b_colored;

        PTRef partialInterpolant;

        InterpolationNodeData() : AB_vars_a_colored(0), AB_vars_b_colored(0), partialInterpolant(PTRef_Undef) {

        }

        inline void clearSharedVar(int varIndex) {
            clrbit(AB_vars_a_colored, varIndex);
            clrbit(AB_vars_b_colored, varIndex);
        }

        inline void    resetLabeling          () { AB_vars_a_colored = 0; AB_vars_b_colored = 0; }
        inline bool    isColoredA             ( int i ) const { return ((tstbit(AB_vars_a_colored, i ) == 1) && (tstbit(AB_vars_b_colored, i ) == 0)); }
        inline bool    isColoredB             ( int i ) const { return ((tstbit(AB_vars_a_colored, i ) == 0) && (tstbit(AB_vars_b_colored, i ) == 1)); }
        inline bool    isColoredAB            ( int i ) const { return ((tstbit(AB_vars_a_colored, i ) == 1) && (tstbit(AB_vars_b_colored, i ) == 1)); }
        inline void    colorA                 ( int i ) { setbit(AB_vars_a_colored, i); clrbit(AB_vars_b_colored, i); }
        inline void    colorB                 ( int i ) { setbit(AB_vars_b_colored, i); clrbit(AB_vars_a_colored, i); }
        inline void    colorAB                ( int i ) { setbit(AB_vars_a_colored, i); setbit(AB_vars_b_colored, i); }
    };

    // NOTE class A has value -1, class B value -2, undetermined value -3, class AB has index bit from 0 onwards
    std::vector<int> AB_vars_mapping;             // Variables of class AB mapping to mpz integer bit index
    std::vector<InterpolationNodeData> nodeData;

public:
    int getSharedVarIndex(Var v) const {
        assert(AB_vars_mapping[v] >= 0);
        return AB_vars_mapping[v];
    }

    icolor_t getVarClass(Var v) const {
        assert((unsigned) v < AB_vars_mapping.size());
        assert(AB_vars_mapping[v] >= -2);
        int c = AB_vars_mapping[v];
        return c == -1 ? icolor_t::I_A : (c == -2 ? icolor_t::I_B : icolor_t::I_AB);
    }

    template<typename TContainer, typename TFun>
    void reset(std::size_t nodeCount, TContainer const & vars, TFun getClass) {
        std::size_t varCounts = (*std::max_element(vars.begin(), vars.end())) + 1;
        nodeData.clear();
        AB_vars_mapping.clear();
        nodeData.resize(nodeCount);
        AB_vars_mapping.resize(varCounts, -3);

        // NOTE class A has value -1, class B value -2, undetermined value -3, class AB has index bit from 0 onwards
        int AB_bit_index = 0;
        for (Var v: vars) {
            icolor_t v_class = getClass(v);
            if (v_class == icolor_t::I_A) { AB_vars_mapping[v] = -1; }
            else if (v_class == icolor_t::I_B) { AB_vars_mapping[v] = -2; }
            else if (v_class == icolor_t::I_AB) {
                AB_vars_mapping[v] = AB_bit_index;
                AB_bit_index++;
            }
            else throw OsmtInternalException("Error in computing variable colors");
        }
    }

    inline bool isColoredA(ProofNode const & n, Var v) const { return nodeData[n.getId()].isColoredA(getSharedVarIndex(v)); }

    inline bool isColoredB(ProofNode const & n, Var v) const { return nodeData[n.getId()].isColoredB(getSharedVarIndex(v)); }

    inline bool isColoredAB(ProofNode const & n, Var v) const { return nodeData[n.getId()].isColoredAB(getSharedVarIndex(v)); }

    inline void colorA(ProofNode & n, Var v) { nodeData[n.getId()].colorA(getSharedVarIndex(v)); }

    inline void colorB(ProofNode & n, Var v) { nodeData[n.getId()].colorB(getSharedVarIndex(v)); }

    inline void colorAB(ProofNode & n, Var v) { nodeData[n.getId()].colorAB(getSharedVarIndex(v)); }

    inline void resetLabeling(ProofNode const & n) { nodeData[n.getId()].resetLabeling(); }

    inline PTRef getPartialInterpolant(ProofNode const & n) { return nodeData[n.getId()].partialInterpolant; }

    inline void setPartialInterpolant(ProofNode const & n, PTRef itp) { nodeData[n.getId()].partialInterpolant = itp; }

    inline void updateColoringfromAnts(ProofNode const & n) {
        assert(not n.isLeaf());
        auto & data = nodeData[n.getId()];
        auto const & ant1Data = nodeData[n.getAnt1()->getId()];
        auto const & ant2Data = nodeData[n.getAnt2()->getId()];
        orbit(data.AB_vars_a_colored, ant1Data.AB_vars_a_colored, ant2Data.AB_vars_a_colored);
        orbit(data.AB_vars_b_colored, ant1Data.AB_vars_b_colored, ant2Data.AB_vars_b_colored);
    }

    inline void clearPivotColoring(ProofNode const & n) {
        assert(not n.isLeaf());
        auto & data = nodeData[n.getId()];
        data.clearSharedVar(getSharedVarIndex(n.getPivot()));
    }
};


class ProofGraph
{
public:

	ProofGraph ( SMTConfig &  c
			, Theory &        th
			, TermMapper &    termMapper
			, Proof const &   proof
			, PartitionManager & pmanager
			, int             n = -1 )
: config   ( c )
, logic_ ( th.getLogic() )
, pmanager (pmanager)
, thandler {new THandler(th, termMapper)}
{
		mpz_init(visited_1);
		mpz_init(visited_2);
		buildProofGraph(proof, n);
		initTSolver();
}

	~ProofGraph()
	{
		mpz_clear(visited_1);
		mpz_clear(visited_2);
		for(size_t i=0;i<getGraphSize();i++)
			if(getNode(i)!=NULL) removeNode(i);
	}

    bool verifyPartialInterpolant(ProofNode*, const ipartitions_t&);
    bool verifyPartialInterpolantA(ProofNode*, const ipartitions_t&);
    bool verifyPartialInterpolantB(ProofNode*, const ipartitions_t&);

    void produceSingleInterpolant           (vec<PTRef>& interpolants, const ipartitions_t& A_mask);
    void printProofAsDotty                  ( std::ostream &);
    //
    // Config
    //
    inline int     verbose                        ( ) const { return config.verbosity(); }
    inline int     produceInterpolants            ( ) const { return config.produce_inter(); }
    inline int     printProofSMT                  ( ) const { return config.print_proofs_smtlib2; }
    inline int     printProofDotty                ( ) const { return config.print_proofs_dotty; }
    inline double  ratioReductionSolvingTime      ( ) const { return config.proof_ratio_red_solv; }
    inline double  reductionTime                  ( ) const { return config.proof_red_time; }
    inline int     reductionLoops                 ( ) const { return config.proof_red_trans(); }
    inline int     numGraphTraversals             ( ) const { return config.proof_num_graph_traversals(); }
    inline int     proofCheck                     ( ) const { return config.proof_check(); }
    bool           enabledInterpVerif             ( ) const { return ( config.certify_inter() >= 1 ); }
    bool           enabledPedInterpVerif          ( ) const { return ( config.certify_inter() >= 2 ); }
    bool           usingMcMillanInterpolation     ( ) const { return config.getBooleanInterpolationAlgorithm() == itp_alg_mcmillan; }
    bool           usingPudlakInterpolation       ( ) const { return config.getBooleanInterpolationAlgorithm() == itp_alg_pudlak; }
    bool           usingMcMillanPrimeInterpolation( ) const { return config.getBooleanInterpolationAlgorithm() == itp_alg_mcmillanp; }
    bool           usingPSInterpolation           ( ) const { return config.getBooleanInterpolationAlgorithm() == itp_alg_ps;  }
    bool           usingPSWInterpolation          ( ) const { return config.getBooleanInterpolationAlgorithm() == itp_alg_psw; }
    bool           usingPSSInterpolation          ( ) const { return config.getBooleanInterpolationAlgorithm() == itp_alg_pss; }

    bool           needProofStatistics            ( ) const { ItpAlgorithm ia = config.getBooleanInterpolationAlgorithm(); return ((ia == itp_alg_ps) || (ia == itp_alg_psw) || (ia == itp_alg_pss)); }
    bool 		    restructuringForStrongerInterpolant	    ( ) { return ( config.proof_trans_strength == 1); }
    bool 		    restructuringForWeakerInterpolant	    ( ) { return ( config.proof_trans_strength == 2); }
    bool		   usingAlternativeInterpolant ( ) { return ( config.proof_alternative_inter() == 1 ); }
    bool			enabledRecyclePivots() { return (config.proof_rec_piv() >= 1); }
    bool			enabledPushDownUnits() { return (config.proof_push_units() >=1); }
    bool			enabledTransfTraversals() { return (config.proof_transf_trav() >= 1); }
    bool			enabledStructuralHashing() { return (config.proof_struct_hash() >= 1); }
    // Inverts the normal order Hashing + RecyclePivots
    bool			switchToRPHashing()			{ return (config.proof_switch_to_rp_hash >= 1);}
    inline bool    additionalRandomization       ( ) { return ( config.proof_random_context_analysis == 1 ); }
    int             simplifyInterpolant () const { return config.getSimplifyInterpolant(); }
    //
    // Build et al.
    //
    void		   emptyProofGraph				 ();					// Empties all clauses besides leaves
    void 		   fillProofGraph				 ();					// Explicitly compute all clauses
    int            cleanProofGraph               ( );                   // Removes proof leftovers
    void           removeNode                    ( clauseid_t );        // Remove node
    unsigned       removeTree                    ( clauseid_t );        // Remove useless subproof
    void		   normalizeAntecedentOrder		 ();					// Make sure ant1 has positive occ pivot
    void           printProofGraph		       		 ();
    // Returns id of new node
    clauseid_t	   	dupliNode					 ( RuleContext& );		// Duplicates w in a context, assign to w only v as child
    //
    // Check et al.
    //
    void           checkClause                        ( clauseid_t );
    // Checks the proof structure; if flag is true, also checks correctness of clause derivations
    void           checkProof                         ( bool check_clauses );
    void 	       checkClauseSorting				  ( clauseid_t );
    void		   checkInterAlgo						();
    //
    // Auxiliary
    //
    inline size_t     getGraphSize              ( ) const { return graph.size( ); }
    bool              isSetVisited1             ( clauseid_t id ) { return mpz_tstbit(visited_1, id); }
    bool              isSetVisited2             ( clauseid_t id ) { return mpz_tstbit(visited_2, id); }
    void              setVisited1               ( clauseid_t id ) { mpz_setbit(visited_1, id); }
    void              setVisited2               ( clauseid_t id ) { mpz_setbit(visited_2, id); }
    void              resetVisited1             ( )               { mpz_set_ui(visited_1,0); }
    void              resetVisited2             ( )               { mpz_set_ui(visited_2,0); }
    bool              isResetVisited1           ( )               { return mpz_cmp_ui(visited_1, 0) == 0; }
    bool              isResetVisited2           ( )               { return mpz_cmp_ui(visited_2, 0) == 0; }

    unsigned          getMaxIdVar           ( ) { return max_id_variable; }
    void              getGraphInfo          ( );
    void              topolSortingTopDown   ( std::vector< clauseid_t > & );
    void              topolSortingBotUp     ( std::vector< clauseid_t > & );
    void              printProofNode        ( clauseid_t );
    void              printClause           (std::ostream&, std::vector<Lit> const& lits);
    void              printClause           ( ProofNode * );
    void              printClause           ( ProofNode *, std::ostream & );
    inline ProofNode* getNode               ( clauseid_t id ) { assert( id<graph.size() ); return graph[ id ]; }
    static bool       mergeClauses          (std::vector<Lit> const &, std::vector<Lit> const &, std::vector<Lit>&, Var);
    inline bool       isRoot                ( ProofNode* n ) { assert(n); return( n->getId() == root ); }
    inline ProofNode* getRoot               ( ) { assert( root<graph.size() );assert(graph[ root ]); return graph[ root ]; }
    inline void       setRoot               ( clauseid_t id ) { assert( id<graph.size() ); root=id; }
    inline void       addLeaf(clauseid_t id)      {  leaves_ids.insert(id); }
    inline void       removeLeaf(clauseid_t id)   {  leaves_ids.erase(id); }
    //
    // Labeling based interpolation
    //
    icolor_t       getVarClass                              ( Var, const ipartitions_t & );
    icolor_t       getClauseColor                           ( CRef clause, const ipartitions_t & );
    std::map<Var, icolor_t>* computePSFunction(std::vector< clauseid_t >& DFSv, const ipartitions_t &);
    void           getPredicatesSetFromInterpolantIterative ( PTRef, std::set<PTRef>& );
    unsigned long  getComplexityInterpolantIterative        ( PTRef, bool );
    // Get formula complexity as number of connectives, number of distinct boolean variables
    void           getComplexityInterpolant( PTRef int_e );
    void           topolSortingEnode                        ( std::vector< PTRef > &, PTRef );

    PTRef computePartialInterpolantForOriginalClause(ProofNode const & n, ipartitions_t const & A_mask);
    PTRef computePartialInterpolantForTheoryClause(ProofNode const & n, ipartitions_t const & A_mask);
    PTRef compInterpLabelingInner                  (ProofNode &);


    icolor_t getPivotColor(ProofNode const &);

    icolor_t getVarColor(ProofNode const & n, Var v);

    void 		   analyzeProofLocality   (const ipartitions_t &);
    void		   verifyLeavesInconsistency ( );
    bool		   decideOnAlternativeInterpolation(ProofNode &);
    // For a given partition mask try to generate interpolants with few predicates
    // Return a vector of interpolants, and for each the set of predicates which was removed
    void 		   removeUnnecessaryPredicates(ipartitions_t & A_mask, std::vector<PTRef>&, std::vector<std::set<PTRef>>&);

    //
    // Trasformation
    //
    enum class ApplicationResult : char { NO_APPLICATION, APPLY_FIRST, APPLY_SECOND};
    bool            chooseReplacingAntecedent( ProofNode* );
    /** A loop of top down reduction sweeps; embeds the topological sorting */
    void            proofTransformAndRestructure(const double, const int, bool do_transf,
                                                    std::function<ApplicationResult(RuleContext&,RuleContext&)> handleRules);
    void            proofPostStructuralHashing();
    double          recyclePivotsIter();
    void            recycleUnits();

    RuleContext     getRuleContext				 (clauseid_t, clauseid_t);
    // In case of A1 rule, return id of node added
    clauseid_t      ruleApply               (RuleContext&);
    clauseid_t      applyRuleA1             (RuleContext&);
    void            applyRuleA1Prime        (RuleContext&);
    void            applyRuleA2             (RuleContext&);
    void            applyRuleB1             (RuleContext&);
    void            applyRuleB2             (RuleContext&);
    void            applyRuleB2Prime        (RuleContext&);
    void            applyRuleB3             (RuleContext&);
    void            printRuleApplicationStatus   ();
    void            transfProofForReduction      ();
    void            transfProofForCNFInterpolants();
    double          doReduction                  (double);
    // Reduce the proof
    ApplicationResult handleRuleApplicationForReduction(RuleContext & ra1, RuleContext & ra2);
    bool            allowSwapRuleForReduction(RuleContext& );
    bool            allowCutRuleForReduction( RuleContext& );
    // Push unit clauses down in the proof
    ApplicationResult handleRuleApplicationForUnitsPushingDown(RuleContext & ra1, RuleContext & ra2);
    bool            allowSwapRuleForUnitsPushingDown(RuleContext&);
    // Push predicates in the proof
    ApplicationResult handleRuleApplicationForPredicatePushing(RuleContext & ra1, RuleContext & ra2);
    bool            allowSwapRuleForPredicatePushingUp( RuleContext&,Var );
    bool            allowSwapRuleForPredicatePushingDown( RuleContext&,Var );
    bool            allowCutRuleForPredicatePushing( RuleContext&,Var );
    inline void     setPredicateToPush(Var p){ pred_to_push = p; }

    // Strengthen/weaken interpolants by applying A2 rule locally
    ApplicationResult handleRuleApplicationForStrongerWeakerInterpolant(RuleContext & ra1, RuleContext & ra2);
    bool            allowSwapRuleForStrongerWeakerInterpolant(RuleContext & ra);
    // Produce interpolants in CNF using McMillan algorithm - partial CNFization since no duplications allowed!
    // See allowSwapRuleForCNFinterpolant
    ApplicationResult handleRuleApplicationForCNFinterpolant(RuleContext & ra1, RuleContext & ra2);
    bool            allowSwapRuleForCNFinterpolant(RuleContext& ra);

private:
    void buildProofGraph(Proof const & proof, int varCount);
    ProofNode * createProofNodeFor(CRef cref, clause_type _ctype, Proof const & proof); // Helper method for building the proof graph

    inline Lit PTRefToLit(PTRef ref) const {return thandler->getTMap().getLit(ref);}
    inline Var PTRefToVar(PTRef ref) const { return thandler->getTMap().getVar(ref); }
    inline PTRef varToPTRef(Var v) const { return thandler->getTMap().varToPTRef(v); }

    void initTSolver();
    void clearTSolver();
    bool assertLiteralsToTSolver(vec<Lit> const &);
    void addDefaultAssumedLiterals(std::vector<Lit> && assumedLiteralsFromDerivations);
    inline bool isAssumedLiteral(Lit l) const {
        return std::find(assumedLiterals.begin(), assumedLiterals.end(), l) != assumedLiterals.end();
    }
    inline bool isAssumedVar(Var v) const {
        return isAssumedLiteral(mkLit(v, true)) or isAssumedLiteral(mkLit(v, false));
    }
    ipartitions_t const& getVarPartition(Var v) const { return pmanager.getIPartitions(varToPTRef(v)); }

    void ensureNoLiteralsWithoutPartition();
    void eliminateNoPartitionTheoryVars(std::vector<Var> const & noParititionTheoryVars);
    void liftVarsToLeaves(std::vector<Var> const & vars);
    void replaceSubproofsWithNoPartitionTheoryVars(std::vector<Var> const & vars);

    void recyclePivotsIter_RecyclePhase();

    // Coloring related methods
    icolor_t getSharedVarColorInNode(Var v, ProofNode const & node) const {
        if (interpolationInfo.isColoredA(node, v)) return icolor_t::I_A;
        else if (interpolationInfo.isColoredB(node, v)) return icolor_t::I_B;
        else if (interpolationInfo.isColoredAB(node, v)) return icolor_t::I_AB;

        throw OsmtInternalException("Variable " + std::to_string(v) + " has no color in clause " + std::to_string(node.getId()));
    }

    PTRef getInterpolantForOriginalClause(ProofNode const & node, icolor_t clauseClass) const;
    std::vector<Lit> getRestrictedNodeClause(ProofNode const & node, icolor_t wantedVarClass) const;

    void labelLeaf(ProofNode & n, std::map<Var, icolor_t> const * PSFunction = nullptr);
    template<typename TFun>
    void setLeafLabeling(ProofNode & node, TFun colorABVar);
    void            setLeafMcMillanLabeling                  (ProofNode &);
    void            setLeafPudlakLabeling                    (ProofNode &);
    void            setLeafMcMillanPrimeLabeling             (ProofNode &);
    void            setLeafPSLabeling		(ProofNode &, std::map<Var, icolor_t> const & PSFunction);
    void            setLeafPSWLabeling		(ProofNode &, std::map<Var, icolor_t> const & PSFunction);
    void            setLeafPSSLabeling		(ProofNode &, std::map<Var, icolor_t> const & PSFunction);

    //NOTE added for experimentation
    Var 				  pred_to_push;

    SMTConfig &                 config;
    Logic &                     logic_;
    PartitionManager &          pmanager;
    std::unique_ptr<THandler>   thandler;
    std::vector<ProofNode *>    graph {};
    double                         building_time;               // Time spent building graph
    clauseid_t                     root;                        // Proof root
    std::set<clauseid_t>		   leaves_ids;					// Proof leaves, for top-down visits
    std::set< Var >                proof_variables;             // Variables actually present in the proof
    unsigned                       max_id_variable;             // Highest value for a variable
    std::set<Var> theory_only;
    std::vector<Lit> assumedLiterals;

    int                            num_vars_limit;               // Number of variables in the problem (not nec in the proof)
    InterpolationInfo interpolationInfo;

    // Info on graph dimension
    int    num_nodes;
    int    num_edges;
    int    num_unary;
    int    num_leaves;

    // Info on clauses
    double av_cla_size;
    double var_cla_size;
    int    max_cla_size;

    // Info on rules application
    unsigned A1;
    unsigned A1prime;
    unsigned A1B;
    unsigned A2;
    unsigned A2B;
    unsigned A2U;
    unsigned B1;
    unsigned B2prime;
    unsigned B2;
    unsigned B3;
    unsigned duplications;
    unsigned swap_ties;

    // Global visit vectors
    mpz_t visited_1;
    mpz_t visited_2;
};

template<typename TFun>
void ProofGraph::setLeafLabeling(ProofNode & node, TFun colorABVar) {
    interpolationInfo.resetLabeling(node);
    std::vector<Lit> const & cl = node.getClause();

    for (Lit l : cl) {
        Var v = var (l);
        icolor_t var_class = interpolationInfo.getVarClass(v);

        if (var_class == icolor_t::I_AB) {
            colorABVar(node, v);
        } else if ( var_class != icolor_t::I_A and var_class != icolor_t::I_B ) {
            OsmtInternalException("Variable has no class");
        }
    }
}

#endif
