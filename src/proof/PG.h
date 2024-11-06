/*
 *  Copyright (c) 2013, Simone Fulvio Rollini <simone.rollini@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef PROOFGRAPH_H
#define PROOFGRAPH_H

#include <common/IColor.h>
#include <smtsolvers/ResolutionProof.h>
#include <pterms/PTRef.h>
#include <logics/Theory.h>
#include <tsolvers/THandler.h>
#include <common/InternalException.h>

#include <functional>
#include <set>

namespace opensmt {

class ResolutionProof;
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
    short hasOccurrenceBin(Var) const;
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

class ProofGraph
{
public:
	ProofGraph ( SMTConfig &  c
            , Logic & logic
            , TermMapper const & termMapper
            , ResolutionProof const &   proof
			)
: config   ( c )
, logic_ ( logic )
, termMapper(termMapper)
{
		mpz_init(visited_1);
		mpz_init(visited_2);
		buildProofGraph(proof);
}

	~ProofGraph()
	{
		mpz_clear(visited_1);
		mpz_clear(visited_2);
		for(size_t i=0;i<getGraphSize();i++)
			if(getNode(i)!=NULL) removeNode(i);
	}

    void printProofAsDotty                  ( std::ostream &);
    //
    // Config
    //
    inline int     verbose                        ( ) const { return config.verbosity(); }
    inline int     printProofSMT                  ( ) const { return config.print_proofs_smtlib2; }
    inline int     printProofDotty                ( ) const { return config.print_proofs_dotty; }
    inline double  ratioReductionSolvingTime      ( ) const { return config.proof_ratio_red_solv; }
    inline double  reductionTime                  ( ) const { return config.proof_red_time; }
    inline int     reductionLoops                 ( ) const { return config.proof_red_trans(); }
    inline int     numGraphTraversals             ( ) const { return config.proof_num_graph_traversals(); }
    inline int     proofCheck                     ( ) const { return config.proof_check(); }


    bool 		    restructuringForStrongerInterpolant	    ( ) { return ( config.proof_trans_strength == 1); }
    bool 		    restructuringForWeakerInterpolant	    ( ) { return ( config.proof_trans_strength == 2); }
    bool			enabledRecyclePivots() { return (config.proof_rec_piv() >= 1); }
    bool			enabledPushDownUnits() { return (config.proof_push_units() >=1); }
    bool			enabledTransfTraversals() { return (config.proof_transf_trav() >= 1); }
    bool			enabledStructuralHashing() { return (config.proof_struct_hash() >= 1); }
    // Inverts the normal order Hashing + RecyclePivots
    bool			switchToRPHashing()			{ return (config.proof_switch_to_rp_hash >= 1);}
    inline bool    additionalRandomization       ( ) { return ( config.proof_random_context_analysis == 1 ); }
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
    //
    // Auxiliary
    //
    inline size_t     getGraphSize              ( ) const { return graph.size( ); }
    bool              isSetVisited1             ( clauseid_t id ) const { return mpz_tstbit(visited_1, id); }
    bool              isSetVisited2             ( clauseid_t id ) const { return mpz_tstbit(visited_2, id); }
    void              setVisited1               ( clauseid_t id ) const { mpz_setbit(visited_1, id); }
    void              setVisited2               ( clauseid_t id ) const { mpz_setbit(visited_2, id); }
    void              resetVisited1             ( ) const               { mpz_set_ui(visited_1,0); }
    void              resetVisited2             ( ) const               { mpz_set_ui(visited_2,0); }
    bool              isResetVisited1           ( ) const               { return mpz_cmp_ui(visited_1, 0) == 0; }
    bool              isResetVisited2           ( ) const               { return mpz_cmp_ui(visited_2, 0) == 0; }

    unsigned          getMaxIdVar           ( ) { return max_id_variable; }
    void              getGraphInfo          ( );

    std::vector<clauseid_t> topolSortingTopDown() const;
    std::vector<clauseid_t> topolSortingBotUp() const;

    std::set<clauseid_t> const & getLeaves() const { return leaves_ids; };
    std::set<Var> const & getVariables() const { return proof_variables; }

    void              printClause           ( ProofNode * );
    void              printClause           ( ProofNode *, std::ostream & );
    inline ProofNode* getNode               ( clauseid_t id ) const { assert(id < graph.size()); return graph[id]; }
    static bool       mergeClauses          (std::vector<Lit> const &, std::vector<Lit> const &, std::vector<Lit>&, Var);
    inline bool       isRoot                ( ProofNode* n ) const { assert(n); return( n->getId() == root ); }
    inline ProofNode* getRoot               ( ) const { assert( root<graph.size() );assert(graph[ root ]); return graph[ root ]; }
    inline void       setRoot               ( clauseid_t id ) { assert( id<graph.size() ); root=id; }

    void		   verifyLeavesInconsistency ( );

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
    void            transfProofForCNFInterpolants(std::function<icolor_t(Var)> getVarClass);
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
    ApplicationResult handleRuleApplicationForStrongerWeakerInterpolant(RuleContext & ra1, RuleContext & ra2, std::function<bool(RuleContext &)> allowSwap);
    bool allowSwapRuleForStrongerWeakerInterpolant(RuleContext & ra, std::function<icolor_t(Var)> getVarClass, bool restructureForStronger);

    // Produce interpolants in CNF using McMillan algorithm - partial CNFization since no duplications allowed!
    // See allowSwapRuleForCNFinterpolant
    ApplicationResult handleRuleApplicationForCNFinterpolant(RuleContext & ra1, RuleContext & ra2, std::function<bool(RuleContext &)> allowSwap);
    bool allowSwapRuleForCNFinterpolant(RuleContext& ra, std::function<icolor_t(Var)>);

    inline bool isAssumedLiteral(Lit l) const {
        return std::find(assumedLiterals.begin(), assumedLiterals.end(), l) != assumedLiterals.end();
    }
    inline bool isAssumedVar(Var v) const {
        return isAssumedLiteral(mkLit(v, true)) or isAssumedLiteral(mkLit(v, false));
    }

    void eliminateNoPartitionTheoryVars(std::vector<Var> const & noParititionTheoryVars);

private:
    void buildProofGraph(ResolutionProof const & proof);
    ProofNode * createProofNodeFor(CRef cref, clause_type _ctype, ResolutionProof const & proof); // Helper method for building the proof graph

    inline void       addLeaf(clauseid_t id)      {  leaves_ids.insert(id); }
    inline void       removeLeaf(clauseid_t id)   {  leaves_ids.erase(id); }

    void addDefaultAssumedLiterals(std::vector<Lit> && assumedLiteralsFromDerivations);

    void liftVarsToLeaves(std::vector<Var> const & vars);
    void replaceSubproofsWithNoPartitionTheoryVars(std::vector<Var> const & vars);

    void recyclePivotsIter_RecyclePhase();


    //NOTE added for experimentation
    Var 				  pred_to_push;

    SMTConfig &                 config;
    Logic &                     logic_;
    TermMapper const &          termMapper;
    std::vector<ProofNode *>    graph {};
    double                         building_time;               // Time spent building graph
    clauseid_t                     root;                        // Proof root
    std::set<clauseid_t>		   leaves_ids;					// Proof leaves, for top-down visits
    std::set< Var >                proof_variables;             // Variables actually present in the proof
    unsigned                       max_id_variable;             // Highest value for a variable
    std::vector<Lit> assumedLiterals;


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
    mutable mpz_t visited_1;
    mutable mpz_t visited_2;
};

}

#endif
