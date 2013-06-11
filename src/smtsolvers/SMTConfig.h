/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
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
  inline void setProduceInter( )  { if ( produce_inter != 0 ) return; produce_inter = 1; }

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

//  int          produce_stats;                // Should print statistics ?
  int          print_stats;                  // Should print statistics ?
  int          produce_models;               // Should produce models ?
  int          produce_proofs;               // Should produce proofs ?
  int          print_proofs_smtlib2;         // Should print proofs ?
  int 	       print_proofs_dotty;	     // Should print proofs ?
  int          produce_inter;                // Should produce interpolants ?
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
  int          sat_restart_first;            // First limit of restart
  double       sat_restart_inc;              // Increment of limit
  int          sat_use_luby_restart;         // Use luby restart mechanism
  int          sat_learn_up_to_size;         // Learn theory clause up to size
  int          sat_temporary_learn;          // Is learning temporary
  int          sat_preprocess_booleans;      // Activate satelite (on booleans)
  int          sat_preprocess_theory;        // Activate theory version of satelite
  int          sat_centrality;               // Specify centrality parameter
  int          sat_trade_off;                // Specify trade off
  int          sat_minimize_conflicts;       // Conflict minimization: 0 none, 1 bool only, 2 full
  int          sat_dump_cnf;                 // Dump cnf formula
  int          sat_dump_rnd_inter;           // Dump random interpolant
  int          sat_lazy_dtc;                 // Activate dtc
  int          sat_lazy_dtc_burst;           // % of eij to generate
  int	       sat_reduce_proof;	     // Enable proof reduction
  int 	       sat_reorder_pivots;	     // Enable pivots reordering for interpolation
  double       sat_ratio_red_time_solv_time; // Reduction time / solving time for each global loop
  double       sat_red_time;                 // Reduction time for each global loop
  int	       sat_num_glob_trans_loops;     // Number of loops recycle pivots + reduction
  int	       sat_remove_mixed;             // Compression of AB-mixed subtrees
  // Proof manipulation parameters
  int          proof_reduce;                 // Enable proof reduction
  double       proof_ratio_red_solv;         // Ratio reduction time solving time for each global loop
  double       proof_red_time;               // Reduction time for each global loop
  int	       proof_num_graph_traversals;   // Number of graph traversals in each global loop
  int          proof_red_trans;              // Number of reduction transformations loops
  int          proof_reorder_pivots;         // Enable pivot reordering
  int 	       proof_reduce_while_reordering;// Enable reduction during reordering
  int	       proof_random_context_analysis;// Examine a context with 50% probability
  int 	       proof_random_swap_application;// Apply a chosen A1,A2,B2k rule with 50% probability
  int          proof_remove_mixed;           // Enable removal of mixed predicates
  int          proof_set_inter_algo;         // 0,1,2 to use McMillan,Pudlak or McMillan' method
  int          proof_certify_inter;          // Check interpolants
  int	       proof_random_seed;	     // Randomly initialize seed for transformation
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
