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

// Interpolation data for resolution proof element
struct InterpolData
{
    PTRef            partial_interp;     // Stores partial interpolant
    ipartitions_t    partition_mask;     // Stores info on partitions in a bitvector

    // NOTE labeling rules for AB variables
    // color a:  bit 1, bit 0
    // color b:  bit 0, bit 1
    // color ab: bit 1, bit 1
    // missing:  bit 0, bit 0
    // This notation is consistent with coloring of inner nodes given by | of antecedents colorings
    ipartitions_t      AB_vars_a_colored;
    ipartitions_t      AB_vars_b_colored;

    InterpolData ()
    : partial_interp    ( PTRef_Undef )
    , partition_mask    ( 0 )
    , AB_vars_a_colored ( 0 )
    , AB_vars_b_colored ( 0 )
    {}
};

// Resolution proof graph element
struct ProofNode
{
    ProofNode    (Logic& _logic)
    : logic      (_logic)
    , clause     (nullptr)
    , clause_ref (CRef_Undef)
    , pivot      (-1)
    , ant1       (nullptr)
    , ant2       (nullptr)
    , resolvents ()
    , i_data     (nullptr)
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
    CRef getClauseRef() { return clause_ref; }

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
    inline std::vector<Lit>&          getClause              ( )       { assert(clause); return *clause; }
    inline std::vector<Lit>*          getPClause             ( )       { return clause; }
    inline size_t                getClauseSize          ( ) const { return clause->size( ); }
    inline Var                   getPivot               ( ) const { return pivot; }
    inline ProofNode *           getAnt1                ( ) const { return ant1; }
    inline ProofNode *           getAnt2                ( ) const { return ant2; }
    inline clause_type           getType                ( ) const { return type; }
    inline PTRef                 getPartialInterpolant  ( ) const { assert(i_data); return i_data->partial_interp; }
    inline const ipartitions_t & getInterpPartitionMask ( ) const { assert(i_data); return i_data->partition_mask; }
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
    inline void                  setPartialInterpolant  ( PTRef new_part_interp )      { assert(i_data); i_data->partial_interp = new_part_interp; }
    void                         setInterpPartitionMask( const ipartitions_t& mask);
    void                         addRes                 ( clauseid_t id )                { resolvents.insert( id ); }
    void                         remRes                 ( clauseid_t id )                { resolvents.erase( id ); }
    void                         initIData() { i_data = new InterpolData(); }
    void                         delIData                ( )                                 { delete i_data; i_data = NULL; }
    //
    // Test methods
    //
    inline bool                  isLeaf(){ assert((ant1==NULL && ant2==NULL) || (ant1!=NULL && ant2!=NULL)); return (ant1==NULL);}
    // 0 if positive, 1 if negative, -1 if not found
    short                         hasOccurrenceBin( Var );
    // true if positive occurrence pivot is in first antecedent
    bool                          checkPolarityAnt();

    //
    // Interpolation and labeling
    //
    inline void    updateColoringfromAnts ()
    {
        orbit( i_data->AB_vars_a_colored, getAnt1()->i_data->AB_vars_a_colored, getAnt2()->i_data->AB_vars_a_colored );
        orbit( i_data->AB_vars_b_colored, getAnt1()->i_data->AB_vars_b_colored, getAnt2()->i_data->AB_vars_b_colored );
    }
    inline void    updateColoringAfterRes ( int i )
    {
        clrbit( i_data->AB_vars_a_colored, i );
        clrbit( i_data->AB_vars_b_colored, i );
    }
    inline void    resetLabeling          () { i_data->AB_vars_a_colored = 0; i_data->AB_vars_b_colored = 0; }
    inline bool    isColoredA             ( int i ) { return ((tstbit(i_data->AB_vars_a_colored, i ) == 1) && (tstbit(i_data->AB_vars_b_colored, i ) == 0)); }
    inline bool    isColoredB             ( int i ) { return ((tstbit(i_data->AB_vars_a_colored, i ) == 0) && (tstbit(i_data->AB_vars_b_colored, i ) == 1)); }
    inline bool    isColoredAB            ( int i ) { return ((tstbit(i_data->AB_vars_a_colored, i ) == 1) && (tstbit(i_data->AB_vars_b_colored, i ) == 1)); }
    inline void    colorA                 ( int i ) { setbit( i_data->AB_vars_a_colored, i ); clrbit( i_data->AB_vars_b_colored, i ); }
    inline void    colorB                 ( int i ) { setbit( i_data->AB_vars_b_colored, i ); clrbit( i_data->AB_vars_a_colored, i ); }
    inline void    colorAB                ( int i ) { setbit( i_data->AB_vars_a_colored, i ); setbit( i_data->AB_vars_b_colored, i ); }

private:
    Logic&             logic;
    clauseid_t         id;                 // id
    std::vector<Lit>*     clause;             // Clause
    CRef clause_ref;
    Var                pivot;              // Non-leaf node pivot
    ProofNode *        ant1;               // Edges to antecedents
    ProofNode *        ant2;               // Edges to antecedents
    std::set<clauseid_t> resolvents;       // Resolvents
    clause_type        type;               // Node type
    InterpolData*      i_data;             // Data for interpolants computation
};


class ProofGraph
{
public:

	ProofGraph ( SMTConfig &  c
			, Theory &        th
			, TermMapper &    termMapper
			, Proof const &   t
			, PartitionManager & pmanager
			, int             n = -1 )
: config   ( c )
, proof	   ( t )
, logic_ ( th.getLogic() )
, pmanager (pmanager)
, thandler {new THandler(th, termMapper)}
, graph_   ( new std::vector<ProofNode*> )
, graph    ( *graph_ )
, vars_suggested_color_map ( NULL )
{
		mpz_init(visited_1);
		mpz_init(visited_2);
		buildProofGraph( n );
		initTSolver();
}

	~ProofGraph()
	{
		mpz_clear(visited_1);
		mpz_clear(visited_2);
		for(size_t i=0;i<getGraphSize();i++)
			if(getNode(i)!=NULL) removeNode(i);
		delete graph_;
	}

    bool verifyPartialInterpolant(ProofNode*, const ipartitions_t&);
    bool verifyPartialInterpolantA(ProofNode*, const ipartitions_t&);
    bool verifyPartialInterpolantB(ProofNode*, const ipartitions_t&);

    bool producePathInterpolants            ( vec<PTRef>& interpolants, const std::vector<ipartitions_t>& A_mask);
    bool producePathInterpolants            ( vec< PTRef > & );
    bool verifyPathInterpolantsFromLeaves   ( vec< PTRef > & );
    bool produceSimultaneousAbstraction     ( vec< PTRef > & );
    bool verifySimultaneousAbstraction      ( vec< PTRef > & );
    bool produceStateTransitionInterpolants ( vec< PTRef > & );
    bool verifyStateTransitionInterpolants  ( vec< PTRef > & );
    bool produceGenSimultaneousAbstraction  ( vec< PTRef > & );
    bool verifyGenSimultaneousAbstraction   ( vec< PTRef > & );
    void produceConfigMatrixInterpolants    ( const std::vector<vec<int> > &,vec<PTRef> &);
    bool produceTreeInterpolants            ( opensmt::InterpolationTree*, vec<PTRef> &);
    bool verifyTreeInterpolantsFromLeaves   ( opensmt::InterpolationTree*, vec<PTRef> &);

    void produceMultipleInterpolants        ( const std::vector< ipartitions_t >&, vec<PTRef> &);
    void produceSingleInterpolant           (vec<PTRef>& interpolants);
    void produceSingleInterpolant           (vec<PTRef>& interpolants, const ipartitions_t& A_mask);
    void printProofAsDotty                  ( std::ostream &, ipartitions_t ip = 0);
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
    bool		   interpolantInCNF							( ) { return ( config.proof_interpolant_cnf() > 0 ); }
    bool		   usingAlternativeInterpolant ( ) { return ( config.proof_alternative_inter() == 1 ); }
    bool			enabledRecyclePivots() { return (config.proof_rec_piv() >= 1); }
    bool			enabledPushDownUnits() { return (config.proof_push_units() >=1); }
    bool			enabledTransfTraversals() { return (config.proof_transf_trav() >= 1); }
    bool			enabledStructuralHashing() { return (config.proof_struct_hash() >= 1); }
    bool			enabledStructuralHashingWhileBuilding() { return (config.proof_struct_hash_build() >= 1); }
    // Inverts the normal order Hashing + RecyclePivots
    bool			switchToRPHashing()			{ return (config.proof_switch_to_rp_hash >= 1);}
    inline bool    additionalRandomization       ( ) { return ( config.proof_random_context_analysis == 1 ); }
    int             simplifyInterpolant () const { return config.getSimplifyInterpolant(); }
    //
    // Build et al.
    //
    void           buildProofGraph               ( int );
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
    icolor_t       getClauseColor                           ( const ipartitions_t &, const ipartitions_t & );
    std::map<Var, icolor_t>* computePSFunction(std::vector< clauseid_t >& DFSv, const ipartitions_t &);
    void           getPredicatesSetFromInterpolantIterative ( PTRef, std::set<PTRef>& );
    unsigned long  getComplexityInterpolantIterative        ( PTRef, bool );
    // Get formula complexity as number of connectives, number of distinct boolean variables
    void           getComplexityInterpolant( PTRef int_e );
    void           topolSortingEnode                        ( std::vector< PTRef > &, PTRef );
    PTRef          compInterpLabelingOriginalSimple         ( ProofNode *, const ipartitions_t & );
    PTRef          compInterpLabelingInnerSimple            ( ProofNode *, const ipartitions_t & );

    PTRef           compInterpLabelingOriginal               (ProofNode * n, const ipartitions_t & A_mask);
    PTRef           compInterpLabelingInner                  (ProofNode *);
    void            labelLeaf                                (ProofNode *, unsigned num_config = 0, std::map<Var, icolor_t>* PSFunc = nullptr);
    void            setLeafRandomLabeling                    (ProofNode *);
    void            setLeafMcMillanLabeling                  (ProofNode *);
    void            setLeafPudlakLabeling                    (ProofNode *);
    void            setLeafMcMillanPrimeLabeling             (ProofNode *);
    void            setLeafPSLabeling		( ProofNode*, std::map<Var, icolor_t>* PSFunction );
    void            setLeafPSWLabeling		( ProofNode*, std::map<Var, icolor_t>* PSFunction );
    void            setLeafPSSLabeling		( ProofNode*, std::map<Var, icolor_t>* PSFunction );
    bool            usingLabelingSuggestions           	    ( ) { return ( config.itp_bool_alg() == 6 ); }
    void            setColoringSuggestions   ( vec< std::map<PTRef, icolor_t>* > * mp ) { assert(mp); vars_suggested_color_map = mp; }
    void            setLabelingFromMap       ( ProofNode*, unsigned );
    icolor_t        getPivotColor                            ( ProofNode * );
    void            computeABVariablesMapping                ( const ipartitions_t & );
    inline int      getVarInfoFromMapping                    ( Var v )
    {
    	assert((unsigned)v<AB_vars_mapping.size()); assert(AB_vars_mapping[v]!=-3);
    	return(AB_vars_mapping[v]);
    }
    // Translation from var info obtained through above function
    icolor_t getVarClass2(Var);
    inline void    resetLabeling          ( ProofNode* n ){ n->resetLabeling(); }
    inline bool    isColoredA             ( ProofNode* n, Var v ) { assert ( AB_vars_mapping[v]>= 0); return n->isColoredA( AB_vars_mapping[v] ); }
    inline bool    isColoredB             ( ProofNode* n, Var v ) { assert ( AB_vars_mapping[v]>= 0); return n->isColoredB( AB_vars_mapping[v] ); }
    inline bool    isColoredAB            ( ProofNode* n, Var v ) { assert ( AB_vars_mapping[v]>= 0); return n->isColoredAB( AB_vars_mapping[v] ); }
    inline void    colorA                 ( ProofNode* n, Var v ) { assert ( AB_vars_mapping[v]>= 0); n->colorA( AB_vars_mapping[v] ); }
    inline void    colorB                 ( ProofNode* n, Var v ) { assert ( AB_vars_mapping[v]>= 0); n->colorB( AB_vars_mapping[v] ); }
    inline void    colorAB                ( ProofNode* n, Var v ) { assert ( AB_vars_mapping[v]>= 0); n->colorAB( AB_vars_mapping[v] ); }
    inline void    updateColoringfromAnts ( ProofNode* n ) { assert(!n->isLeaf()); n->updateColoringfromAnts(); }
    inline void    updateColoringAfterRes ( ProofNode* n )
    {
    	assert(!n->isLeaf()); assert( AB_vars_mapping[n->getPivot()]>= 0);
    	n->updateColoringAfterRes( AB_vars_mapping[n->getPivot()] );
    }
    icolor_t getVarColor(ProofNode* n, Var v);

    void 		   analyzeProofLocality   (const ipartitions_t &);
    void 		   verifyPartialInterpolantFromLeaves ( ProofNode*, const ipartitions_t& mask );
    void		   verifyLeavesInconsistency ( );
    void  		   verifyInductiveSequence ( );
    bool		   decideOnAlternativeInterpolation(ProofNode*);
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
    void            printRuleApplicationStatus  ();
    void            transfProofForReduction     ();
    double          doIt                        (double);
    double          doReduction                 (double);
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

    inline Lit PTRefToLit(PTRef ref) const {return thandler->getTMap().getLit(ref);}
    inline Var PTRefToVar(PTRef ref) const { return thandler->getTMap().getVar(ref); }
    inline PTRef varToPTRef(Var v) const { return thandler->getTMap().varToPTRef(v); }

    void initTSolver();
    void clearTSolver();
    bool assertLiteralsToTSolver(vec<Lit> const&);
    void addDefaultAssumedLiterals();
    inline bool isAssumedLiteral(Lit l) const {
        return std::find(assumedLiterals.begin(), assumedLiterals.end(), l) != assumedLiterals.end();
    }
    inline bool isAssumedVar(Var v) const {
        return isAssumedLiteral(mkLit(v, true)) || isAssumedLiteral(mkLit(v, false));
    }
    ipartitions_t const& getVarPartition(Var v) const { return pmanager.getIPartitions(varToPTRef(v)); }

    void ensureNoLiteralsWithoutPartition();
    void eliminateNoPartitionTheoryVars(std::vector<Var> const & noParititionTheoryVars);
    void liftVarsToLeaves(std::vector<Var> const & vars);
    void replaceSubproofsWithNoPartitionTheoryVars(std::vector<Var> const & vars);

    void recyclePivotsIter_RecyclePhase();

    //NOTE added for experimentation
    Var 				  pred_to_push;

    SMTConfig &                 config;
    Proof const &               proof;
    Logic &                     logic_;
    PartitionManager &          pmanager;
    std::unique_ptr<THandler>   thandler;

    std::vector< ProofNode * >*    graph_;                      // Graph
    std::vector< ProofNode * >&    graph;
    double                         building_time;               // Time spent building graph
    clauseid_t                     root;                        // Proof root
    std::set<clauseid_t>		   leaves_ids;					// Proof leaves, for top-down visits
    std::set< Var >                proof_variables;             // Variables actually present in the proof
    unsigned                       max_id_variable;             // Highest value for a variable
    std::set<Var> theory_only;
    std::vector<Lit> assumedLiterals;
    // NOTE class A has value -1, class B value -2, undetermined value -3, class AB has index bit from 0 onwards
    std::vector<int>               AB_vars_mapping;             // Variables of class AB mapping to mpz integer bit index
    vec< std::map<PTRef, icolor_t>* > *    vars_suggested_color_map;	 // To suggest color for shared vars
    int                            num_vars_limit;               // Number of variables in the problem (not nec in the proof)

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

#endif
