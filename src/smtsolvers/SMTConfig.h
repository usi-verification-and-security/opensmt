/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#ifndef SMTCONFIG_H
#define SMTCONFIG_H

#include "Global.h"
#include "SolverTypes.h"
#include "parsers/smt2new/smt2newcontext.h"
#include "common/StringMap.h"

enum ConfType { O_EMPTY, O_STR, O_SYM, O_NUM, O_DEC, O_HEX, O_BIN, O_LIST, O_ATTR, O_BOOL };

class ConfValue {
  public:
    ConfType type;
    union { char* strval; int numval; double decval; uint32_t unumval; list<ConfValue*>* configs; };
    ConfValue() : type(O_EMPTY) {};
    ConfValue(const ASTNode& s_expr_n);
    ConfValue(int i) : type(O_DEC), numval(i) {};
    ConfValue(const char* s);
    char* toString() const;
};

class Info {
  private:
//    char*      name;
    ConfValue   value;
  public:
    Info(ASTNode& n);
    Info() {};
    bool isEmpty() const { return value.type == O_EMPTY; }
    inline char* toString() const { return value.toString(); };
};


class Option {
  private:
    ConfValue   value;
  public:
    Option(ASTNode& n);
    Option() {}
    Option(int i)   : value(i) {}
    Option(const char* s) : value(s) {}
    inline bool  isEmpty()  const { return value.type == O_EMPTY; }
    inline char* toString() const { return value.toString(); }
    inline const ConfValue& getValue() const { return value; }
};

//
// Holds informations about the configuration of the solver
//
struct SMTConfig
{
private:
  static const char* o_incremental;
  static const char* o_produce_stats;
  static const char* o_stats_out;
  static const char* o_random_seed;
  // Allow a variable elimination step to grow by a number of clauses.
  static const char* o_grow;
  //Variables are not eliminated if it produces a resolvent with a length above this limit. -1 means no limit
  static const char* o_clause_lim;
  // Do not check if subsumption against a clause larger than this. -1 means no limit.
  static const char* o_subsumption_lim;
  // The fraction of wasted memory allowed before a garbage collection is triggered during simplification.
  static const char* o_simp_garbage_frac;
  // Shrink clauses by asymmetric branching.
  static const char* o_use_asymm;
  // Check if a clause is already implied. (costly)
  static const char* o_use_rcheck;
  // Perform variable elimination.
  static const char* o_use_elim;
  static const char* o_var_decay;
  static const char* o_clause_decay;
  static const char* o_random_var_freq;
  static const char* o_luby_restart;
  static const char* o_ccmin_mode;
  static const char* o_phase_saving;
  static const char* o_rnd_pol;
  static const char* o_rnd_init_act;
  static const char* o_garbage_frac;
  static const char* o_restart_first;
  static const char* o_restart_inc;
  static const char* o_produce_inter;
  static const char* o_proof_struct_hash;
  static const char* o_proof_num_graph_traversals;
  static const char* o_proof_red_trans;
  static const char* o_proof_rec_piv;
  static const char* o_proof_push_units;
  static const char* o_proof_transf_trav;
  static const char* o_proof_struct_hash_build;
  static const char* o_proof_check;
  static const char* o_proof_multiple_inter;
  static const char* o_proof_alternative_inter;
  static const char* o_proof_reduce;
  static const char* o_proof_set_inter_algo;
  static const char* o_sat_dump_rnd_inter;
  static const char* o_sat_time_limit;
  static const char* o_sat_dec_limit;
  static const char* o_dump_state;
  static const char* o_dump_only;
private:
  Info          info_Empty;
  Option        option_Empty;
  Map<const char*,Info,StringHash,Equal<const char*> >   infoTable;
  Map<const char*,Option,StringHash,Equal<const char*> > optionTable;
  //
  // For standard executable
  //
public:
  SMTConfig ( int    argc
	    , char * argv[ ] )
    : filename ( argv[ argc - 1 ] )
    , rocset   ( false )
    , docset   ( false )
  {
    initializeConfig( );
    // Parse command-line options
    parseCMDLine( argc, argv );
  }
  //
  // For API
  //
  SMTConfig ( )
    : filename ( NULL )
    , rocset   ( false )
    , docset   ( false )
  {
    initializeConfig( );
  }

  ~SMTConfig ( )
  {
    if ( produceStats() )  stats_out.close( );
    if ( rocset )         out.close( );
    if ( docset )         err.close( );
  }

  bool          setOption(const char* name, const Option& value);
  const Option& getOption(const char* name) const;

  bool          setInfo  (const char* name, const Info& value);
  const Info&   getInfo  (const char* name) const;

  void initializeConfig ( );

  void parseConfig      ( char * );
  void parseCMDLine     ( int argc, char * argv[ ] );
  void printHelp        ( );
  void printConfig      ( ostream & out );

  inline bool      isInit      ( ) { return logic != UNDEF; }

  inline ostream & getStatsOut     ( ) { assert( optionTable.contains(o_produce_stats) );  return stats_out; }
  inline ostream & getRegularOut   ( ) { return rocset ? out : cout; }
  inline ostream & getDiagnosticOut( ) { return docset ? err : cerr; }
  inline int       getRandomSeed   ( ) { return optionTable.contains(o_random_seed) ? optionTable[o_random_seed].getValue().numval : 91648253; }

  inline void setProduceModels( ) { if ( produce_models != 0 ) return; produce_models = 1; }
  inline void setProduceProofs( ) { if ( print_proofs_smtlib2 != 0 ) return; print_proofs_smtlib2 = 1; }

  inline void setRegularOutputChannel( const char * attr )
  {
    if ( strcmp( attr, "stdout" ) != 0 && !rocset )
    {
      out.open( attr );
      if( !out )
        opensmt_error2( "can't open ", attr );
      rocset = true;
    }
  }

  inline void setDiagnosticOutputChannel( const char * attr )
  {
    if ( strcmp( attr, "stderr" ) != 0 && !rocset )
    {
      err.open( attr );
      if( !err )
	opensmt_error2( "can't open ", attr );
      rocset = true;
    }
  }

  const char * filename;                     // Holds the name of the input filename
  logic_t      logic;                        // SMT-Logic under consideration
  lbool	       status;                       // Status of the benchmark
//  int          incremental;                  // Incremental solving
  int           isIncremental() const
     { return optionTable.contains(o_incremental) ?
        optionTable[o_incremental].getValue().numval == 1: false; }
  int          produceStats() const
     { return optionTable.contains(o_produce_stats) ?
        optionTable[o_produce_stats].getValue().numval == 1: false; }
  std::string  getStatsOut() const
     { return optionTable.contains(o_stats_out) ?
        optionTable[o_stats_out].getValue().strval: "/dev/stdout"; }

  int sat_grow() const
    { return optionTable.contains(o_grow) ?
        optionTable[o_grow].getValue().numval : 0; }
  int sat_clause_lim() const
    { return optionTable.contains(o_clause_lim) ?
        optionTable[o_clause_lim].getValue().numval : 20; }
  int sat_subsumption_lim() const
    { return optionTable.contains(o_subsumption_lim) ?
        optionTable[o_subsumption_lim].getValue().numval : 1000; }
  double sat_simp_garbage_frac() const
    { return optionTable.contains(o_simp_garbage_frac) ?
        optionTable[o_simp_garbage_frac].getValue().decval : 0.5; }
  int sat_use_asymm() const
    { return optionTable.contains(o_use_asymm) ?
        optionTable[o_use_asymm].getValue().numval == 1: false; }
  int sat_use_rcheck() const
    { return optionTable.contains(o_use_rcheck) ?
        optionTable[o_use_rcheck].getValue().numval == 1: false; }
  int sat_use_elim() const
    { return optionTable.contains(o_use_elim) ?
        optionTable[o_use_elim].getValue().numval == 1: true; }
  int sat_var_decay() const
    { return optionTable.contains(o_var_decay) ?
        optionTable[o_var_decay].getValue().decval : 1 / 0.95; }
  int sat_clause_decay() const
    { return optionTable.contains(o_clause_decay) ?
        optionTable[o_clause_decay].getValue().decval : 1 / 0.999; }
  int sat_random_var_freq() const
    { return optionTable.contains(o_random_var_freq) ?
        optionTable[o_random_var_freq].getValue().decval : 0.02; }
  int sat_random_seed() const
    { return optionTable.contains(o_random_seed) ?
        optionTable[o_random_seed].getValue().decval : 91648253; }
  int sat_luby_restart() const
    { return optionTable.contains(o_luby_restart) ?
        optionTable[o_luby_restart].getValue().numval > 0 : 1; }
  int sat_ccmin_mode() const
    { return optionTable.contains(o_ccmin_mode) ?
        optionTable[o_ccmin_mode].getValue().numval : 2; }
  int sat_pcontains() const
    { return optionTable.contains(o_phase_saving) ?
        optionTable[o_phase_saving].getValue().numval : 2; }
  int sat_rnd_pol() const
    { return optionTable.contains(o_rnd_pol) ?
        optionTable[o_rnd_pol].getValue().numval > 0 : 0; }
  int sat_rnd_init_act() const
    { return optionTable.contains(o_rnd_init_act) ?
        optionTable[o_rnd_init_act].getValue().numval > 0 : 0; }
  double sat_garbage_frac() const
    { return optionTable.contains(o_garbage_frac) ?
        optionTable[o_garbage_frac].getValue().decval : 0.20; }
  int sat_restart_first() const
    { return optionTable.contains(o_restart_first) ?
        optionTable[o_restart_first].getValue().numval : 100; }
  double sat_restart_inc() const
    { return optionTable.contains(o_restart_inc) ?
        optionTable[o_restart_inc].getValue().numval : 1.1; }
  int produce_inter() const
    { return optionTable.contains(o_produce_inter) ?
        optionTable[o_produce_inter].getValue().numval : 0; }
  int proof_struct_hash() const
    { return optionTable.contains(o_proof_struct_hash) ?
        optionTable[o_proof_struct_hash].getValue().numval : 1; }
  int proof_num_graph_traversals() const
    { return optionTable.contains(o_proof_num_graph_traversals) ?
        optionTable[o_proof_num_graph_traversals].getValue().numval : 3; }
  int proof_red_trans() const
    { return optionTable.contains(o_proof_red_trans) ?
        optionTable[o_proof_red_trans].getValue().numval : 2; }
  int proof_rec_piv() const
    { return optionTable.contains(o_proof_rec_piv) ?
        optionTable[o_proof_rec_piv].getValue().numval : 1; }
  int proof_push_units() const
    { return optionTable.contains(o_proof_push_units) ?
        optionTable[o_proof_push_units].getValue().numval : 1; }
  int proof_transf_trav() const
    { return optionTable.contains(o_proof_transf_trav) ?
        optionTable[o_proof_transf_trav].getValue().numval : 1; }
  int proof_struct_hash_build() const
    { return optionTable.contains(o_proof_struct_hash_build) ?
        optionTable[o_proof_struct_hash_build].getValue().numval : 0; }
  int proof_check() const
    { return optionTable.contains(o_proof_check) ?
        optionTable[o_proof_check].getValue().numval : 0; }
  int proof_multiple_inter() const
    { return optionTable.contains(o_proof_multiple_inter) ?
        optionTable[o_proof_multiple_inter].getValue().numval : 0; }
  int proof_alternative_inter() const
    { return optionTable.contains(o_proof_alternative_inter) ?
        optionTable[o_proof_alternative_inter].getValue().numval : 0; }
  int proof_reduce() const
    { return optionTable.contains(o_proof_reduce) ?
        optionTable[o_proof_reduce].getValue().numval : 0; }
  int proof_set_inter_algo() const
    { return optionTable.contains(o_proof_set_inter_algo) ?
        optionTable[o_proof_set_inter_algo].getValue().numval : 1; }
  int sat_dump_rnd_inter() const
    { return optionTable.contains(o_sat_dump_rnd_inter) ?
        optionTable[o_sat_dump_rnd_inter].getValue().numval : 2; }
  int sat_time_limit() const
    { return optionTable.contains(o_sat_time_limit) ?
        optionTable[o_sat_time_limit].getValue().numval : -1; }
  int sat_dec_limit() const
    { return optionTable.contains(o_sat_dec_limit) ?
        optionTable[o_sat_dec_limit].getValue().numval : -1; }
  const char* dump_state() const
    { return optionTable.contains(o_dump_state) ?
        optionTable[o_dump_state].getValue().strval : "out.osmt2"; }
  int dump_only() const
    { return optionTable.contains(o_dump_only) ?
        optionTable[o_dump_only].getValue().numval : 0; }

//  int          produce_stats;                // Should print statistics ?
  int          print_stats;                  // Should print statistics ?
  int          produce_models;               // Should produce models ?
  int          produce_proofs;               // Should produce proofs ?
  int          print_proofs_smtlib2;         // Should print proofs ?
  int 	       print_proofs_dotty;	     // Should print proofs ?
  bool         rocset;                       // Regular Output Channel set ?
  bool         docset;                       // Diagnostic Output Channel set ?
  int          dump_formula;                 // Dump input formula
  int          verbosity() const             // Verbosity level
#ifdef PEDANTIC_DEBUG
    { return optionTable.contains(":verbosity") ?
        optionTable[":verbosity"].getValue().numval : 2; }
#elif GC_DEBUG
    { return optionTable.contains(":verbosity") ?
        optionTable[":verbosity"].getValue().numval : 2; }
#else
    { return optionTable.contains(":verbosity") ?
        optionTable[":verbosity"].getValue().numval : 0; }
#endif
  int          printSuccess() const
     { return optionTable.contains(":print-success") ?
        optionTable[":print-success"].getValue().numval == 1: false; }
  int          certification_level;          // Level of certification
  char         certifying_solver[256];       // Executable used for certification
  // SAT-Solver related parameters
  int          sat_theory_propagation;       // Enables theory propagation from the sat-solver
  int          sat_polarity_mode;            // Polarity mode
  double       sat_initial_skip_step;        // Initial skip step for tsolver calls
  double       sat_skip_step_factor;         // Increment for skip step
  int          sat_use_luby_restart;         // Use luby restart mechanism
  int          sat_learn_up_to_size;         // Learn theory clause up to size
  int          sat_temporary_learn;          // Is learning temporary
  int          sat_preprocess_booleans;      // Activate satelite (on booleans)
  int          sat_preprocess_theory;        // Activate theory version of satelite
  int          sat_centrality;               // Specify centrality parameter
  int          sat_trade_off;                // Specify trade off
  int          sat_minimize_conflicts;       // Conflict minimization: 0 none, 1 bool only, 2 full
  int          sat_dump_cnf;                 // Dump cnf formula
  int          sat_lazy_dtc;                 // Activate dtc
  int          sat_lazy_dtc_burst;           // % of eij to generate
  int	       sat_reduce_proof;	     // Enable proof reduction
  int 	       sat_reorder_pivots;	     // Enable pivots reordering for interpolation
  double       sat_ratio_red_time_solv_time; // Reduction time / solving time for each global loop
  double       sat_red_time;                 // Reduction time for each global loop
  int	       sat_num_glob_trans_loops;     // Number of loops recycle pivots + reduction
  int	       sat_remove_mixed;             // Compression of AB-mixed subtrees
  int		   sat_propagate_small;			 // Try to propagate first smaller clauses
  int		   sat_restart_learnt_thresh;    // Restart solver if the current learnt has width > thresh
  int		   sat_orig_thresh;				 // Allows original clauses of width up to thresh
  // Proof manipulation parameters
  double       proof_ratio_red_solv;         // Ratio reduction time solving time for each global loop
  double       proof_red_time;               // Reduction time for each global loop
  int          proof_reorder_pivots;         // Enable pivot reordering
  int 	       proof_reduce_while_reordering;// Enable reduction during reordering
  int	       proof_random_context_analysis;// Examine a context with 50% probability
  int 	       proof_random_swap_application;// Apply a chosen A1,A2,B2k rule with 50% probability
  int          proof_remove_mixed;           // Enable removal of mixed predicates
  int          proof_certify_inter;          // Check interpolants
  int	       proof_random_seed;	     // Randomly initialize seed for transformation
//   int		   proof_rec_piv;				 // Enable the use of RecyclePivots for reduction
//  int		   proof_push_units;			// Enable pushing down units heuristics
//  int          proof_struct_hash_build;		 // Enable structural hashing while building the proof
//  int 		   proof_struct_hash;			 // Enable structural hashing for compression
  int 		   proof_switch_to_rp_hash;		 // Instead of hashing + rp does the opposite
//  int 		   proof_transf_trav;			 // Enable transformation traversals
//  int		   proof_check;					 // Enable proof checking
//  int		   proof_alternative_inter;		 // Dual formula for AB pivots
//  int		   proof_multiple_inter;		 // Multiple interpolants
  int          proof_interpolant_cnf;		 // Enable proof restructuring for interpolant in CNF
  int          proof_trans_strength;		 // Light proof restructuring for stronger/weaker interpolants, for Pudlak/McMillan/McMillan' algorithms
  // UF-Solver related parameters
  int          uf_disable;                   // Disable the solver
  int          uf_theory_propagation;        // Enable theory propagation
  // BV-Solver related parameters
  int          bv_disable;                   // Disable the solver
  int          bv_theory_propagation;        // Enable theory propagation
  // DL-Solver related parameters
  int          dl_disable;                   // Disable the solver
  int          dl_theory_propagation;        // Enable theory propagation
  // LRA-Solver related parameters
  int          lra_disable;                  // Disable the solver
  int          lra_theory_propagation;       // Enable theory propagation
  int          lra_poly_deduct_size;         // Used to define the size of polynomial to be used for deduction; 0 - no deduction for polynomials
  int          lra_trade_off;                // Trade-off value for DL preprocessing
  int          lra_gaussian_elim;            // Used to switch on/off Gaussian elimination in LRA
  int          lra_integer_solver;           // Flag to require integer solution for LA problem
  int          lra_check_on_assert;          // Probability (0 to 100) to run check when assert is called

private:

  ofstream     stats_out;                    // File for statistics
  ofstream     out;                          // Regular output channel
  ofstream     err;                          // Diagnostic output channel
};
#endif
