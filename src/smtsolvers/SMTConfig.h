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
    ConfValue() : type(O_EMPTY), strval(NULL) {};
    ConfValue(const ASTNode& s_expr_n);
    ConfValue(int i) : type(O_DEC), numval(i) {};
    ConfValue(double i) : type(O_DEC), decval(i) {};
    ConfValue(const char* s);
    ConfValue(const ConfValue& other);
    ConfValue& operator=(const ConfValue& other);
    char* toString() const;
    double getDoubleVal() const {if (type == O_NUM) return (double)numval; else if (type == O_DEC) return decval; else assert(false); return -1;}
    ~ConfValue();
};

class Info {
  private:
    ConfValue   value;
  public:
    Info(ASTNode& n);
    Info(const Info& other);
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
    Option(double i): value(i) {}
    Option(const char* s) : value(s) {}
    inline bool  isEmpty()  const { return value.type == O_EMPTY; }
    inline char* toString() const { return value.toString(); }
    inline const ConfValue& getValue() const { return value; }
};

// Type safe wrapper for split types
typedef struct SpType    { int t; } SpType;
typedef struct SpUnit    { int t; } SpUnit;
typedef struct SpPref    { int t; } SpPref;

inline bool operator==(const SpType& s1, const SpType& s2) { return s1.t == s2.t; }
inline bool operator==(const SpUnit& s1, const SpUnit& s2) { return s1.t == s2.t; }
inline bool operator!=(const SpType& s1, const SpType& s2) { return s1.t != s2.t; }
inline bool operator!=(const SpUnit& s1, const SpUnit& s2) { return s1.t != s2.t; }
inline bool operator==(const SpPref& s1, const SpPref& s2) { return s1.t == s2.t; }
inline bool operator!=(const SpPref& s1, const SpPref& s2) { return s1.t != s2.t; }

static const char* spts_lookahead = "lookahead";
static const char* spts_scatter   = "scattering";
static const char* spts_none      = "none";

static const char* spts_decisions = "decisions";
static const char* spts_time      = "time";

static const char* spprefs_tterm   = "tterm";
static const char* spprefs_blind   = "blind";
static const char* spprefs_bterm   = "bterm";
static const char* spprefs_rand    = "random";

static const struct SpType spt_none      = { 0 };
static const struct SpType spt_lookahead = { 1 };
static const struct SpType spt_scatter   = { 2 };

static const struct SpUnit spm_decisions = { 0 };
static const struct SpUnit spm_time      = { 1 };
static const struct SpUnit spm_unknown   = { 2 };


static const struct SpPref sppref_tterm = { 0 };
static const struct SpPref sppref_blind = { 1 };
static const struct SpPref sppref_bterm = { 2 };
static const struct SpPref sppref_rand  = { 3 };
static const struct SpPref sppref_undef = { 4 };

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
  static const char* o_sat_resource_units;
  static const char* o_sat_resource_limit;
  static const char* o_dump_state;
  static const char* o_dump_only;
  static const char* o_sat_dump_learnts;
  static const char* o_sat_split_type;
  static const char* o_sat_split_inittune;
  static const char* o_sat_split_midtune;
  static const char* o_sat_split_num;
  static const char* o_sat_split_asap;
  static const char* o_sat_split_units;
  static const char* o_sat_split_preference;
  static const char* o_produce_models;
  static const char* o_sat_remove_symmetries;

  static const char* s_err_not_str;
  static const char* s_err_not_bool;
  static const char* s_err_not_num;
  static const char* s_err_seed_zero;
  static const char* s_err_unknown_split;
  static const char* s_err_unknown_units;

private:
  Info          info_Empty;
  Option        option_Empty;
  vec<Option*>  options;
  vec<char*>    option_names;
  vec<Info*>    infos;
  vec<char*>    info_names;
  Map<const char*,Info*,StringHash,Equal<const char*> >   infoTable;
  Map<const char*,Option*,StringHash,Equal<const char*> > optionTable;
  void          insertOption(const char* o_name, Option* o) {
      options.push(o);
      if (optionTable.contains(o_name)) optionTable[o_name] = o;
      else {
          char* my_name = strdup(o_name);
          option_names.push(my_name);
          optionTable.insert(my_name, o);
      }
  }
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
    for (int i = 0; i < options.size(); i++)
        delete options[i];
    for (int i = 0; i < option_names.size(); i++)
        free(option_names[i]);
    for (int i = 0; i < infos.size(); i++)
        delete infos[i];
    for (int i = 0; i < info_names.size(); i++)
        free(info_names[i]);
  }

  bool          setOption(const char* name, const Option& value, const char*& msg);
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
  inline int       getRandomSeed   ( ) { return optionTable.contains(o_random_seed) ? optionTable[o_random_seed]->getValue().numval : 91648253; }
  inline bool      produceModel    ( ) { return optionTable.contains(o_produce_models) ? optionTable[o_produce_models]->getValue().numval == 1 : true; }
  inline void setProduceModels( ) { insertOption(o_produce_models, new Option(1)); }
  inline bool setRandomSeed(int seed) { insertOption(o_random_seed, new Option(seed)); }

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
  struct Logic_t logic;                        // SMT-Logic under consideration
  lbool	       status;                       // Status of the benchmark
//  int          incremental;                  // Incremental solving
  int           isIncremental() const
     { return optionTable.contains(o_incremental) ?
        optionTable[o_incremental]->getValue().numval == 1: false; }
  int produce_models() const {
      return optionTable.contains(o_produce_models) ?
              optionTable[o_produce_models]->getValue().numval :
              1; }
  int          produceStats() const
     { return optionTable.contains(o_produce_stats) ?
        optionTable[o_produce_stats]->getValue().numval == 1: false; }
  std::string  getStatsOut() const
     { return optionTable.contains(o_stats_out) ?
        optionTable[o_stats_out]->getValue().strval: "/dev/stdout"; }

  int sat_grow() const
    { return optionTable.contains(o_grow) ?
        optionTable[o_grow]->getValue().numval : 0; }
  int sat_clause_lim() const
    { return optionTable.contains(o_clause_lim) ?
        optionTable[o_clause_lim]->getValue().numval : 20; }
  int sat_subsumption_lim() const
    { return optionTable.contains(o_subsumption_lim) ?
        optionTable[o_subsumption_lim]->getValue().numval : 1000; }
  double sat_simp_garbage_frac() const
    { return optionTable.contains(o_simp_garbage_frac) ?
        optionTable[o_simp_garbage_frac]->getValue().decval : 0.5; }
  int sat_use_asymm() const
    { return optionTable.contains(o_use_asymm) ?
        optionTable[o_use_asymm]->getValue().numval == 1: false; }
  int sat_use_rcheck() const
    { return optionTable.contains(o_use_rcheck) ?
        optionTable[o_use_rcheck]->getValue().numval == 1: false; }
  int sat_use_elim() const
    { return optionTable.contains(o_use_elim) ?
        optionTable[o_use_elim]->getValue().numval == 1: true; }
  int sat_var_decay() const
    { return optionTable.contains(o_var_decay) ?
        optionTable[o_var_decay]->getValue().decval : 1 / 0.95; }
  int sat_clause_decay() const
    { return optionTable.contains(o_clause_decay) ?
        optionTable[o_clause_decay]->getValue().decval : 1 / 0.999; }
  int sat_random_var_freq() const
    { return optionTable.contains(o_random_var_freq) ?
        optionTable[o_random_var_freq]->getValue().decval : 0.02; }
  int sat_random_seed() const
    { return optionTable.contains(o_random_seed) ?
        optionTable[o_random_seed]->getValue().decval : 91648253; }
  int sat_luby_restart() const
    { return optionTable.contains(o_luby_restart) ?
        optionTable[o_luby_restart]->getValue().numval > 0 : 1; }
  int sat_ccmin_mode() const
    { return optionTable.contains(o_ccmin_mode) ?
        optionTable[o_ccmin_mode]->getValue().numval : 2; }
  int sat_pcontains() const
    { return optionTable.contains(o_phase_saving) ?
        optionTable[o_phase_saving]->getValue().numval : 2; }
  int sat_rnd_pol() const
    { return optionTable.contains(o_rnd_pol) ?
        optionTable[o_rnd_pol]->getValue().numval > 0 : 0; }
  int sat_rnd_init_act() const
    { return optionTable.contains(o_rnd_init_act) ?
        optionTable[o_rnd_init_act]->getValue().numval > 0 : 0; }
  double sat_garbage_frac() const
    { return optionTable.contains(o_garbage_frac) ?
        optionTable[o_garbage_frac]->getValue().decval : 0.20; }
  int sat_restart_first() const
    { return optionTable.contains(o_restart_first) ?
        optionTable[o_restart_first]->getValue().numval : 100; }
  double sat_restart_inc() const
    { return optionTable.contains(o_restart_inc) ?
        optionTable[o_restart_inc]->getValue().numval : 1.1; }
  int produce_inter() const
    { return optionTable.contains(o_produce_inter) ?
        optionTable[o_produce_inter]->getValue().numval : 0; }
  int proof_struct_hash() const
    { return optionTable.contains(o_proof_struct_hash) ?
        optionTable[o_proof_struct_hash]->getValue().numval : 1; }
  int proof_num_graph_traversals() const
    { return optionTable.contains(o_proof_num_graph_traversals) ?
        optionTable[o_proof_num_graph_traversals]->getValue().numval : 3; }
  int proof_red_trans() const
    { return optionTable.contains(o_proof_red_trans) ?
        optionTable[o_proof_red_trans]->getValue().numval : 2; }
  int proof_rec_piv() const
    { return optionTable.contains(o_proof_rec_piv) ?
        optionTable[o_proof_rec_piv]->getValue().numval : 1; }
  int proof_push_units() const
    { return optionTable.contains(o_proof_push_units) ?
        optionTable[o_proof_push_units]->getValue().numval : 1; }
  int proof_transf_trav() const
    { return optionTable.contains(o_proof_transf_trav) ?
        optionTable[o_proof_transf_trav]->getValue().numval : 1; }
  int proof_struct_hash_build() const
    { return optionTable.contains(o_proof_struct_hash_build) ?
        optionTable[o_proof_struct_hash_build]->getValue().numval : 0; }
  int proof_check() const
    { return optionTable.contains(o_proof_check) ?
        optionTable[o_proof_check]->getValue().numval : 0; }
  int proof_multiple_inter() const
    { return optionTable.contains(o_proof_multiple_inter) ?
        optionTable[o_proof_multiple_inter]->getValue().numval : 0; }
  int proof_alternative_inter() const
    { return optionTable.contains(o_proof_alternative_inter) ?
        optionTable[o_proof_alternative_inter]->getValue().numval : 0; }
  int proof_reduce() const
    { return optionTable.contains(o_proof_reduce) ?
        optionTable[o_proof_reduce]->getValue().numval : 0; }
  int proof_set_inter_algo() const
    { return optionTable.contains(o_proof_set_inter_algo) ?
        optionTable[o_proof_set_inter_algo]->getValue().numval : 1; }
  int sat_dump_rnd_inter() const
    { return optionTable.contains(o_sat_dump_rnd_inter) ?
        optionTable[o_sat_dump_rnd_inter]->getValue().numval : 2; }

  const SpUnit sat_resource_units() const {
      if (optionTable.contains(o_sat_resource_units)) {
          const char* type = optionTable[o_sat_resource_units]->getValue().strval;
          if (strcmp(type, spts_decisions) == 0)
              return spm_decisions;
          else if (strcmp(type, spts_time) == 0)
              return spm_time;
      }
      return spm_unknown;
    }
  double sat_resource_limit() const
    { return optionTable.contains(o_sat_resource_limit) ?
        optionTable[o_sat_resource_limit]->getValue().getDoubleVal() : -1; }
  const char* dump_state() const
    { return optionTable.contains(o_dump_state) ?
        optionTable[o_dump_state]->getValue().strval : "out.osmt2"; }
  int dump_only() const
    { return optionTable.contains(o_dump_only) ?
        optionTable[o_dump_only]->getValue().numval : 0; }
  int sat_dump_learnts() const
    { return optionTable.contains(o_sat_dump_learnts) ?
        optionTable[o_sat_dump_learnts]->getValue().numval : 0; }

    bool sat_split_threads(int threads){
        if (threads<1 || parallel_threads) return false;
        insertOption(o_sat_split_type, new Option(spts_scatter));
        //insertOption(o_sat_split_type, new Option(spts_lookahead));
        insertOption(o_sat_split_units, new Option(spts_time));
        insertOption(o_sat_split_inittune, new Option(double(2)));
        insertOption(o_sat_split_midtune, new Option(double(2)));
        insertOption(o_sat_split_num, new Option(threads));
        insertOption(o_sat_split_asap, new Option(1));
        parallel_threads = threads;
        return true;
    }

  const SpType sat_split_type() const {
      if (optionTable.contains(o_sat_split_type)) {
        const char* type = optionTable[o_sat_split_type]->getValue().strval;
        if (strcmp(type, spts_lookahead) == 0)
            return spt_lookahead;
        else if (strcmp(type, spts_scatter) == 0)
            return spt_scatter;
      }
      return spt_none; }

  const SpUnit sat_split_units() const {
      if (optionTable.contains(o_sat_split_units)) {
          const char* type = optionTable[o_sat_split_units]->getValue().strval;
          if (strcmp(type, spts_decisions) == 0)
              return spm_decisions;
          else if (strcmp(type, spts_time) == 0)
              return spm_time;
      }
      return spm_decisions;
    }

  double sat_split_inittune() const {
      return optionTable.contains(o_sat_split_inittune) ?
              optionTable[o_sat_split_inittune]->getValue().getDoubleVal() :
              -1; }
  double sat_split_midtune() const {
      return optionTable.contains(o_sat_split_midtune) ?
              optionTable[o_sat_split_midtune]->getValue().getDoubleVal() :
              -1; }
  int sat_split_num() const {
      return optionTable.contains(o_sat_split_num) ?
              optionTable[o_sat_split_num]->getValue().numval :
              -1; }
  int sat_split_asap() const {
      return optionTable.contains(o_sat_split_asap) ?
              optionTable[o_sat_split_asap]->getValue().numval :
              0; }

  int remove_symmetries() const
    { return optionTable.contains(o_sat_remove_symmetries) ?
        optionTable[o_sat_remove_symmetries]->getValue().numval : 0; }

  SpPref sat_split_preference() const {
    if (optionTable.contains(o_sat_split_preference)) {
        const char* type = optionTable[o_sat_split_preference]->getValue().strval;
        if (strcmp(type, spprefs_tterm) == 0) return sppref_tterm;
        if (strcmp(type, spprefs_blind) == 0) return sppref_blind;
        if (strcmp(type, spprefs_bterm) == 0) return sppref_bterm;
        if (strcmp(type, spprefs_rand)  == 0) return sppref_rand;
    } else return sppref_blind;
  }


//  int          produce_stats;                // Should print statistics ?
  int          print_stats;                  // Should print statistics ?
  int          produce_proofs;               // Should produce proofs ?
  int          print_proofs_smtlib2;         // Should print proofs ?
  int 	       print_proofs_dotty;	     // Should print proofs ?
  bool         rocset;                       // Regular Output Channel set ?
  bool         docset;                       // Diagnostic Output Channel set ?
  int          dump_formula;                 // Dump input formula
  int          verbosity() const             // Verbosity level
#ifdef PEDANTIC_DEBUG
    { return optionTable.contains(":verbosity") ?
        optionTable[":verbosity"]->getValue().numval : 2; }
#elif GC_DEBUG
    { return optionTable.contains(":verbosity") ?
        optionTable[":verbosity"]->getValue().numval : 2; }
#else
    { return optionTable.contains(":verbosity") ?
        optionTable[":verbosity"]->getValue().numval : 2; }
#endif
  int          printSuccess() const
     { return optionTable.contains(":print-success") ?
        optionTable[":print-success"]->getValue().numval == 1: false; }
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

  // parameter for parallelism
  int          parallel_threads;

    static char* server_host;
    static uint16_t server_port;
    static char* database_host;
    static uint16_t database_port;


private:

  ofstream     stats_out;                    // File for statistics
  ofstream     out;                          // Regular output channel
  ofstream     err;                          // Diagnostic output channel
};
#endif
