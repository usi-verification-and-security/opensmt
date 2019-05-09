/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2016 Antti Hyvarinen
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
#include "StringMap.h"
#include "smt2tokens.h"
#include <libgen.h>

enum ASTType {
      CMD_T      , CMDL_T
    , SYM_T      , SYML_T
    , NUM_T      , NUML_T
    , SORT_T     , SORTL_T
    , SV_T       , SVL_T
    , UATTR_T    , UATTRL_T
    , PATTR_T    , PATTRL_T
    , GATTR_T    , GATTRL_T
    , SPECC_T    , SPECCL_T
    , SEXPR_T    , SEXPRL_T
    , ID_T       , IDL_T
    , LID_T      , LIDL_T
    , DEC_T      , DECL_T
    , HEX_T      , HEXL_T
    , BIN_T      , BINL_T
    , STR_T      , STRL_T
    , AS_T       , ASL_T
    , VARB_T     , VARBL_T
    , TERM_T     , TERML_T
    , QID_T      , QITL_T
    , LQID_T     , LQIDL_T
    , LET_T      , LETL_T
    , FORALL_T   , FORALLL_T
    , EXISTS_T   , EXISTSL_T
    , BANG_T     , BANGL_T
    , SSYMD_T    , SSYMDL_T
    , FSYMD_T    , FSYMDL_T
    , PFSYMD_T   , PFSYMDL_T
    , PFID_T     , PFIDL_T
    , TATTR_T    , TATTRL_T
    , TDECL_T    , TDECLL_T
    , LATTR_T    , LATTRL_T
    , LOGIC_T    , LOGICL_T
    , BOOL_T     , BOOLL_T
    , OPTION_T   , OPTIONL_T
    , INFO_T     , INFOL_T
    , CONST_T    , CONSTL_T
};

class ASTNode {
  private:
    ASTType             type;
    smt2token           tok;
    char*               val;
    static const char*  typestr[];
  public:
    std::list< ASTNode* >*children;
    ASTNode(ASTType t, smt2token tok) : type(t), tok(tok), val(NULL), children(NULL) {}
    ASTNode(ASTType t, char* v) : type(t), tok({t_none}), val(v), children(NULL) {}
    ~ASTNode() {
        if (children) {
            for (std::list<ASTNode*>::const_iterator ci = children->begin(); ci != children->end(); ci++) {
                delete *ci;
            };
            delete children;
        }
        free(val);
    }
    void                  print(std::ostream& o, int indent);
    inline const char      *typeToStr() const { return typestr[type]; }
    inline ASTType         getType()   const { return type; }
    inline const char      *getValue()  const { return val; }
    inline const smt2token getToken()  const { return tok; }
};


enum ConfType { O_EMPTY, O_STR, O_SYM, O_NUM, O_DEC, O_HEX, O_BIN, O_LIST, O_ATTR, O_BOOL };

class ConfValue {
  public:
    ConfType type;
    union { char* strval; int numval; double decval; uint32_t unumval; list<ConfValue*>* configs; };
    ConfValue() : type(O_EMPTY), strval(NULL) {};
    ConfValue(const ASTNode& s_expr_n);
    ConfValue(int i) : type(O_NUM), numval(i) {};
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

class SMTOption {
  private:
    ConfValue   value;
  public:
    SMTOption(ASTNode& n);
    SMTOption() {}
    SMTOption(int i)   : value(i) {}
    SMTOption(double i): value(i) {}
    SMTOption(const char* s) : value(s) {}
    inline bool  isEmpty()  const { return value.type == O_EMPTY; }
    inline char* toString() const { return value.toString(); }
    inline const ConfValue& getValue() const { return value; }
};

// Type safe wrapper for split types
typedef struct SpType    { int t; } SpType;
typedef struct SpUnit    { int t; } SpUnit;
typedef struct SpPref    { int t; } SpPref;

typedef struct SpFormat  { int t; } SpFormat;

struct ItpAlgorithm { int x; bool operator==(const ItpAlgorithm& o) const { return x == o.x; }};
static const struct ItpAlgorithm itp_alg_mcmillan  = { 0 };
static const struct ItpAlgorithm itp_alg_pudlak    = { 1 };
static const struct ItpAlgorithm itp_alg_mcmillanp = { 2 };
static const struct ItpAlgorithm itp_alg_ps        = { 3 };
static const struct ItpAlgorithm itp_alg_psw       = { 4 };
static const struct ItpAlgorithm itp_alg_pss       = { 5 };
static const struct ItpAlgorithm itp_euf_alg_strong  = { 0 };
static const struct ItpAlgorithm itp_euf_alg_weak  = { 2 };
static const struct ItpAlgorithm itp_euf_alg_random  = { 3 };
static const struct ItpAlgorithm itp_lra_alg_strong  = { 0 };
static const struct ItpAlgorithm itp_lra_alg_weak  = { 2 };
static const struct ItpAlgorithm itp_lra_alg_factor  = { 3 };
static const struct ItpAlgorithm itp_lra_alg_experimental_strong  = { 4 };
static const struct ItpAlgorithm itp_lra_alg_experimental_weak  = { 5 };
static const char *itp_lra_factor_0 = "1/2";

inline bool operator==(const SpType& s1, const SpType& s2) { return s1.t == s2.t; }
inline bool operator==(const SpUnit& s1, const SpUnit& s2) { return s1.t == s2.t; }
inline bool operator!=(const SpType& s1, const SpType& s2) { return s1.t != s2.t; }
inline bool operator!=(const SpUnit& s1, const SpUnit& s2) { return s1.t != s2.t; }
inline bool operator==(const SpPref& s1, const SpPref& s2) { return s1.t == s2.t; }
inline bool operator!=(const SpPref& s1, const SpPref& s2) { return s1.t != s2.t; }
inline bool operator==(const SpFormat& s1, const SpFormat& s2) { return s1.t == s2.t; }
inline bool operator!=(const SpFormat& s1, const SpFormat& s2) { return s1.t != s2.t; }

static const char* const spts_lookahead = "lookahead";
static const char* const spts_scatter   = "scattering";
static const char* const spts_none      = "none";

static const char* const spts_decisions = "decisions";
static const char* const spts_time      = "time";

static const char* const spprefs_tterm   = "tterm";
static const char* const spprefs_blind   = "blind";
static const char* const spprefs_bterm   = "bterm";
static const char* const spprefs_rand    = "random";

static const char* const spformats_brief  = "brief";
static const char* const spformats_full   = "full";

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

static const struct SpFormat spformat_smt2  = { 0 };
static const struct SpFormat spformat_osmt2 = { 1 };
static const struct SpFormat spformat_brief = { 2 };
static const struct SpFormat spformat_full  = { 3 };

//
// Holds informations about the configuration of the solver
//
struct SMTConfig
{
  // The options here should be private
public:
  static const char* o_incremental;
  static const char* o_verbosity;
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
  static const char* o_certify_inter;
  static const char* o_interpolant_cnf;
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
  static const char* o_itp_bool_alg;
  static const char* o_itp_euf_alg;
  static const char* o_itp_lra_alg;
  static const char* o_itp_lra_factor;
  static const char* o_sat_dump_rnd_inter;
  static const char* o_sat_resource_units;
  static const char* o_sat_resource_limit;
  static const char* o_dump_state;
  static const char* o_time_queries;
  static const char* o_inst_name;
  static const char* o_dump_only;
  static const char* o_dump_mode;
  static const char* o_dump_query;
  static const char* o_dump_query_name;
  static const char* o_sat_dump_learnts;
  static const char* o_sat_split_type;
  static const char* o_sat_split_inittune;
  static const char* o_sat_split_midtune;
  static const char* o_sat_split_num;
  static const char* o_sat_split_fix_vars; // Like split_num, but give the number of vars to fix instead
  static const char* o_sat_split_asap;
  static const char* o_sat_lookahead_split;
  static const char* o_sat_pure_lookahead;
  static const char* o_sat_split_units;
  static const char* o_sat_split_preference;
  static const char* o_sat_split_test_cube_and_conquer;
  static const char* o_sat_split_randomize_lookahead;
  static const char* o_sat_split_randomize_lookahead_buf;
  static const char* o_produce_models;
  static const char* o_sat_remove_symmetries;
  static const char* o_dryrun;
  static const char* o_do_substitutions;
  static const char* o_smt_split_format;
  static const char* o_smt_split_format_length;
  static const char* o_respect_logic_partitioning_hints;
  static const char* o_output_dir;

private:

  static const char* s_err_not_str;
  static const char* s_err_not_bool;
  static const char* s_err_not_num;
  static const char* s_err_seed_zero;
  static const char* s_err_unknown_split;
  static const char* s_err_unknown_units;


  Info          info_Empty;
  SMTOption        option_Empty;
  vec<SMTOption*>  options;
  vec<char*>    option_names;
  vec<Info*>    infos;
  vec<char*>    info_names;
  Map<const char*,Info*,StringHash,Equal<const char*> >   infoTable;
  Map<const char*,SMTOption*,StringHash,Equal<const char*> > optionTable;
  void          insertOption(const char* o_name, SMTOption* o) {
      options.push(o);
      if (optionTable.has(o_name)) optionTable[o_name] = o;
      else {
          char* my_name = strdup(o_name);
          option_names.push(my_name);
          optionTable.insert(my_name, o);
      }
  }
  char* append_output_dir(const char* name) const
  {
      const char* path = output_dir();
      // If output_dir() is not defined (or is empty), just return (copy of) name
      if (strlen(path) == 0)
          return strdup(name);
      // Otherwise, use name but prepend output_dir.
      char* tmp_name = strdup(name);
      char* base = basename(tmp_name);
      int full_length = strlen(base)+1+strlen(output_dir());
      char *full_str = (char*)malloc(full_length+1);
      char* ptr = full_str;
      for (unsigned int i = 0; i < strlen(path); i++) {
          *ptr = path[i];
          ptr++;
      }
      (*ptr) = '/';
      ptr++;
      for (unsigned int i = 0; i < strlen(base); i++) {
          *ptr = base[i];
          ptr++;
      }
      *ptr = '\0';
      free(tmp_name);
      return full_str;
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

  bool             setOption(const char* name, const SMTOption& value, const char*& msg);
  const SMTOption& getOption(const char* name) const;

  bool          setInfo  (const char* name, const Info& value);
  const Info&   getInfo  (const char* name) const;

  void initializeConfig ( );

  void parseConfig      ( char * );
  void parseCMDLine     ( int argc, char * argv[ ] );
  void printHelp        ( );
  void printConfig      ( ostream & out );

  inline bool      isInit      ( ) { return logic != opensmt::Logic_t::UNDEF; }

  inline ostream & getStatsOut     ( ) { assert( optionTable.has(o_produce_stats) );  return stats_out; }
  inline ostream & getRegularOut   ( ) { return rocset ? out : cout; }
  inline ostream & getDiagnosticOut( ) { return docset ? err : cerr; }
  inline int       getRandomSeed   ( ) { return optionTable.has(o_random_seed) ? optionTable[o_random_seed]->getValue().numval : 91648253; }
  inline bool      produceModel    ( ) { return optionTable.has(o_produce_models) ? optionTable[o_produce_models]->getValue().numval == 1 : true; }
  inline void setProduceModels( ) { insertOption(o_produce_models, new SMTOption(1)); }
  inline bool setRandomSeed(int seed) { insertOption(o_random_seed, new SMTOption(seed)); return true; }

  inline void setProduceProofs( ) { if ( print_proofs_smtlib2 != 0 ) return; print_proofs_smtlib2 = 1; }

  void setTimeQueries() { insertOption(o_time_queries, new SMTOption(1)); }
  bool timeQueries()    { return optionTable.has(o_time_queries) ? optionTable[o_time_queries]->getValue().numval : false; }
  // Set reduction params
  inline void setReduction(int r) { insertOption(o_proof_reduce, new SMTOption(r)); }

  inline void setReductionGraph(int r) { insertOption(o_proof_num_graph_traversals, new SMTOption(r)); }

  inline void setReductionLoops(int r) { insertOption(o_proof_red_trans, new SMTOption(r)); }

  // Set interpolation algorithms
  inline void setBooleanInterpolationAlgorithm( ItpAlgorithm i ) { 
      insertOption(o_itp_bool_alg, new SMTOption(i.x)); }

  inline void setEUFInterpolationAlgorithm( ItpAlgorithm i ) { insertOption(o_itp_euf_alg, new SMTOption(i.x)); }

  inline void setLRAInterpolationAlgorithm( ItpAlgorithm i ) { insertOption(o_itp_lra_alg, new SMTOption(i.x)); }

  inline void setLRAStrengthFactor(const char *factor) { insertOption(o_itp_lra_factor, new SMTOption(factor)); }

  inline void setInstanceName(const char* name) { insertOption(o_inst_name, new SMTOption(name)); }

  // Get interpolation algorithms
  inline ItpAlgorithm getBooleanInterpolationAlgorithm() {
      if (optionTable.has(o_itp_bool_alg)) { return { optionTable[o_itp_bool_alg]->getValue().numval }; }
      else { return itp_alg_mcmillan; }}

  inline ItpAlgorithm getEUFInterpolationAlgorithm() {
      if (optionTable.has(o_itp_euf_alg)) { return { optionTable[o_itp_euf_alg]->getValue().numval }; }
      else { return itp_euf_alg_strong; }}

  inline ItpAlgorithm getLRAInterpolationAlgorithm() {
      if (optionTable.has(o_itp_lra_alg)) { return { optionTable[o_itp_lra_alg]->getValue().numval }; }
      else { return itp_lra_alg_strong; }}

  inline const char* getLRAStrengthFactor() {
      if (optionTable.has(o_itp_lra_factor)) { return optionTable[o_itp_lra_factor]->getValue().strval; }
      else { return itp_lra_factor_0; }
  }

  inline const char* getInstanceName() const {
      if (optionTable.has(o_inst_name))  { return optionTable[o_inst_name]->getValue().strval; }
      else { return "unknown"; }
  }

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
  opensmt::Logic_t logic;                    // SMT-Logic under consideration
  lbool        status;                       // Status of the benchmark
//  int          incremental;                  // Incremental solving
  int           isIncremental() const
     { return optionTable.has(o_incremental) ?
        optionTable[o_incremental]->getValue().numval == 1: true; }
  int produce_models() const {
      return optionTable.has(o_produce_models) ?
              optionTable[o_produce_models]->getValue().numval :
              1; }
  int          produceStats() const
     { return optionTable.has(o_produce_stats) ?
        optionTable[o_produce_stats]->getValue().numval == 1: false; }
  std::string  getStatsOut() const
     { return optionTable.has(o_stats_out) ?
        optionTable[o_stats_out]->getValue().strval: "/dev/stdout"; }

  int sat_grow() const
    { return optionTable.has(o_grow) ?
        optionTable[o_grow]->getValue().numval : 0; }
  int sat_clause_lim() const
    { return optionTable.has(o_clause_lim) ?
        optionTable[o_clause_lim]->getValue().numval : 20; }
  int sat_subsumption_lim() const
    { return optionTable.has(o_subsumption_lim) ?
        optionTable[o_subsumption_lim]->getValue().numval : 1000; }
  double sat_simp_garbage_frac() const
    { return optionTable.has(o_simp_garbage_frac) ?
        optionTable[o_simp_garbage_frac]->getValue().decval : 0.5; }
  int sat_use_asymm() const
    { return optionTable.has(o_use_asymm) ?
        optionTable[o_use_asymm]->getValue().numval == 1: false; }
  int sat_use_rcheck() const
    { return optionTable.has(o_use_rcheck) ?
        optionTable[o_use_rcheck]->getValue().numval == 1: false; }
  int sat_use_elim() const
    { return optionTable.has(o_use_elim) ?
        optionTable[o_use_elim]->getValue().numval == 1: true; }
  double sat_var_decay() const
    { return optionTable.has(o_var_decay) ?
        optionTable[o_var_decay]->getValue().decval : 1 / 0.95; }
  double sat_clause_decay() const
    { return optionTable.has(o_clause_decay) ?
        optionTable[o_clause_decay]->getValue().decval : 1 / 0.999; }
  double sat_random_var_freq() const
    { return optionTable.has(o_random_var_freq) ?
        optionTable[o_random_var_freq]->getValue().decval : 0.02; }
  int sat_random_seed() const
    { return optionTable.has(o_random_seed) ?
        optionTable[o_random_seed]->getValue().decval : 91648253; }
  int sat_luby_restart() const
    { return optionTable.has(o_luby_restart) ?
        optionTable[o_luby_restart]->getValue().numval > 0 : 1; }
  int sat_ccmin_mode() const
    { return optionTable.has(o_ccmin_mode) ?
        optionTable[o_ccmin_mode]->getValue().numval : 2; }
  int sat_pcontains() const
    { return optionTable.has(o_phase_saving) ?
        optionTable[o_phase_saving]->getValue().numval : 2; }
  int sat_rnd_pol() const
    { return optionTable.has(o_rnd_pol) ?
        optionTable[o_rnd_pol]->getValue().numval > 0 : 0; }
  int sat_rnd_init_act() const
    { return optionTable.has(o_rnd_init_act) ?
        optionTable[o_rnd_init_act]->getValue().numval > 0 : 0; }
  double sat_garbage_frac() const
    { return optionTable.has(o_garbage_frac) ?
        optionTable[o_garbage_frac]->getValue().decval : 0.20; }
  int sat_restart_first() const
    { return optionTable.has(o_restart_first) ?
        optionTable[o_restart_first]->getValue().numval : 100; }
  double sat_restart_inc() const
    { return optionTable.has(o_restart_inc) ?
        optionTable[o_restart_inc]->getValue().numval : 1.1; }
  int proof_interpolant_cnf() const
  { return optionTable.has(o_interpolant_cnf) ?
      optionTable[o_interpolant_cnf]->getValue().numval : 0; }
  int certify_inter() const
    { return optionTable.has(o_certify_inter) ?
        optionTable[o_certify_inter]->getValue().numval : 0; }
  int produce_inter() const
    { return optionTable.has(o_produce_inter) ?
        optionTable[o_produce_inter]->getValue().numval : 0; }
  int proof_struct_hash() const
    { return optionTable.has(o_proof_struct_hash) ?
        optionTable[o_proof_struct_hash]->getValue().numval : 1; }
  int proof_num_graph_traversals() const
    { return optionTable.has(o_proof_num_graph_traversals) ?
        optionTable[o_proof_num_graph_traversals]->getValue().numval : 3; }
  int proof_red_trans() const
    { return optionTable.has(o_proof_red_trans) ?
        optionTable[o_proof_red_trans]->getValue().numval : 2; }
  int proof_rec_piv() const
    { return optionTable.has(o_proof_rec_piv) ?
        optionTable[o_proof_rec_piv]->getValue().numval : 1; }
  int proof_push_units() const
    { return optionTable.has(o_proof_push_units) ?
        optionTable[o_proof_push_units]->getValue().numval : 1; }
  int proof_transf_trav() const
    { return optionTable.has(o_proof_transf_trav) ?
        optionTable[o_proof_transf_trav]->getValue().numval : 1; }
  int proof_struct_hash_build() const
    { return optionTable.has(o_proof_struct_hash_build) ?
        optionTable[o_proof_struct_hash_build]->getValue().numval : 0; }
  int proof_check() const
    { return optionTable.has(o_proof_check) ?
        optionTable[o_proof_check]->getValue().numval : 0; }
  int proof_multiple_inter() const
    { return optionTable.has(o_proof_multiple_inter) ?
        optionTable[o_proof_multiple_inter]->getValue().numval : 0; }
  int proof_alternative_inter() const
    { return optionTable.has(o_proof_alternative_inter) ?
        optionTable[o_proof_alternative_inter]->getValue().numval : 0; }
  int proof_reduce() const
    { return optionTable.has(o_proof_reduce) ?
        optionTable[o_proof_reduce]->getValue().numval : 0; }
  int itp_bool_alg() const
    { return optionTable.has(o_itp_bool_alg) ?
        optionTable[o_itp_bool_alg]->getValue().numval : 0; }
  int itp_euf_alg() const
    { return optionTable.has(o_itp_euf_alg) ?
        optionTable[o_itp_euf_alg]->getValue().numval : 0; }
  int itp_lra_alg() const
    { return optionTable.has(o_itp_lra_alg) ?
        optionTable[o_itp_lra_alg]->getValue().numval : 0; }
  int sat_dump_rnd_inter() const
    { return optionTable.has(o_sat_dump_rnd_inter) ?
        optionTable[o_sat_dump_rnd_inter]->getValue().numval : 2; }

  const SpUnit sat_resource_units() const {
      if (optionTable.has(o_sat_resource_units)) {
          const char* type = optionTable[o_sat_resource_units]->getValue().strval;
          if (strcmp(type, spts_decisions) == 0)
              return spm_decisions;
          else if (strcmp(type, spts_time) == 0)
              return spm_time;
      }
      return spm_unknown;
    }
  const SpFormat smt_split_format_length() const {
      if (optionTable.has(o_smt_split_format_length)) {
          const char* type = optionTable[o_smt_split_format_length]->getValue().strval;
          if (strcmp(type, spformats_brief) == 0)
              return spformat_brief;
          else if (strcmp(type, spformats_full) == 0)
              return spformat_full;
      }
      return spformat_full; // The default
    }
  bool respect_logic_partitioning_hints() const
  { return optionTable.has(o_respect_logic_partitioning_hints) ?
      optionTable[o_respect_logic_partitioning_hints]->getValue().numval : 0; }
  double sat_resource_limit() const
    { return optionTable.has(o_sat_resource_limit) ?
        optionTable[o_sat_resource_limit]->getValue().getDoubleVal() : -1; }

  char* dump_state() const
    {
        char* n;
        if (optionTable.has(o_dump_state))
            n = strdup(optionTable[o_dump_state]->getValue().strval);
        else {
            const char* name = getInstanceName();
            int name_length = strlen(name)-strlen(".smt2");
            n = (char*)malloc(name_length+1);
            for (int i = 0; i < name_length; i++)
                n[i] = name[i];
            n[name_length] = '\0';
        }
        char* name = append_output_dir(n);
        free(n);
        return name;
    }
  const char* output_dir() const
    {
        if (optionTable.has(o_output_dir))
            return optionTable[o_output_dir]->getValue().strval;
        else
            return "";
    }
  int dump_only() const
    { return optionTable.has(o_dump_only) ?
        optionTable[o_dump_only]->getValue().numval : 0; }
  bool dump_query() const
    { return optionTable.has(o_dump_query) ?
        optionTable[o_dump_query]->getValue().numval : 0; }

  void set_dump_query_name(const char* dump_query_name)
    {
        if (optionTable.has(o_dump_query_name)) {
            delete optionTable[o_dump_query_name];
            optionTable[o_dump_query_name] = new SMTOption(strdup(dump_query_name));
        }
        else
            insertOption(o_dump_query_name, new SMTOption(strdup(dump_query_name)));
    }
  char* dump_query_name() const
    {
        char* n;
        if (optionTable.has(o_dump_query_name))
            n = strdup(optionTable[o_dump_query_name]->getValue().strval);
        else {
            return NULL;
        }
        char* name = append_output_dir(n);
        free(n);
        return name;
    }

  int sat_dump_learnts() const
    { return optionTable.has(o_sat_dump_learnts) ?
        optionTable[o_sat_dump_learnts]->getValue().numval : 0; }

  bool sat_split_test_cube_and_conquer() const
    { return optionTable.has(o_sat_split_test_cube_and_conquer) ?
        optionTable[o_sat_split_test_cube_and_conquer]->getValue().numval : 0; }

  const SpType sat_split_type() const {
      if (sat_lookahead_split())
          return spt_lookahead;
      if (optionTable.has(o_sat_split_type)) {
        const char* type = optionTable[o_sat_split_type]->getValue().strval;
        if (strcmp(type, spts_lookahead) == 0)
            return spt_lookahead;
        else if (strcmp(type, spts_scatter) == 0)
            return spt_scatter;
      }
      return spt_none; }

  const SpUnit sat_split_units() const {
      if (optionTable.has(o_sat_split_units)) {
          const char* type = optionTable[o_sat_split_units]->getValue().strval;
          if (strcmp(type, spts_decisions) == 0)
              return spm_decisions;
          else if (strcmp(type, spts_time) == 0)
              return spm_time;
      }
      return spm_decisions;
    }

  double sat_split_inittune() const {
      return optionTable.has(o_sat_split_inittune) ?
              optionTable[o_sat_split_inittune]->getValue().getDoubleVal() :
              -1; }
  double sat_split_midtune() const {
      return optionTable.has(o_sat_split_midtune) ?
              optionTable[o_sat_split_midtune]->getValue().getDoubleVal() :
              -1; }
  int sat_split_num() const {
      return optionTable.has(o_sat_split_num) ?
              optionTable[o_sat_split_num]->getValue().numval :
              2; }
  int sat_split_fixvars() const {
      return optionTable.has(o_sat_split_fix_vars) ?
              optionTable[o_sat_split_fix_vars]->getValue().numval :
              -1; }
  int sat_split_asap() const {
      return optionTable.has(o_sat_split_asap) ?
              optionTable[o_sat_split_asap]->getValue().numval :
              0; }
  int sat_lookahead_split() const {
      return optionTable.has(o_sat_lookahead_split) ?
              optionTable[o_sat_lookahead_split]->getValue().numval :
              0; }
  int sat_pure_lookahead() const {
      return optionTable.has(o_sat_pure_lookahead) ?
              optionTable[o_sat_pure_lookahead]->getValue().numval :
              0; }
  int randomize_lookahead() const {
      return optionTable.has(o_sat_split_randomize_lookahead) ?
              optionTable[o_sat_split_randomize_lookahead]->getValue().numval :
              0; }

  int randomize_lookahead_bufsz() const {
      return optionTable.has(o_sat_split_randomize_lookahead_buf) ?
              optionTable[o_sat_split_randomize_lookahead_buf]->getValue().numval :
              1; }

  int remove_symmetries() const
    { return optionTable.has(o_sat_remove_symmetries) ?
        optionTable[o_sat_remove_symmetries]->getValue().numval : 0; }

  int dryrun() const
    { return optionTable.has(o_dryrun) ?
        optionTable[o_dryrun]->getValue().numval : 0; }

  void set_dryrun(bool b)
    { insertOption(o_dryrun, new SMTOption(b)); }

  SpPref sat_split_preference() const {
    if (optionTable.has(o_sat_split_preference)) {
        const char* type = optionTable[o_sat_split_preference]->getValue().strval;
        if (strcmp(type, spprefs_tterm) == 0) return sppref_tterm;
        if (strcmp(type, spprefs_blind) == 0) return sppref_blind;
        if (strcmp(type, spprefs_bterm) == 0) return sppref_bterm;
        if (strcmp(type, spprefs_rand)  == 0) return sppref_rand;
    }
      return sppref_blind;
  }
  int do_substitutions() const
    { return optionTable.has(o_do_substitutions) ?
        optionTable[o_do_substitutions]->getValue().numval : 1; }


//  int          produce_stats;                // Should print statistics ?
  int          print_stats;                  // Should print statistics ?
  int          produce_proofs;               // Should produce proofs ?
  int          print_proofs_smtlib2;         // Should print proofs ?
  int          print_proofs_dotty;           // Should print proofs ?
  bool         rocset;                       // Regular Output Channel set ?
  bool         docset;                       // Diagnostic Output Channel set ?
  int          dump_formula;                 // Dump input formula
  int          verbosity() const             // Verbosity level
// TODO: remove MACROS from header file
#ifdef PEDANTIC_DEBUG
    { return optionTable.has(o_verbosity) ?
        optionTable[o_verbosity]->getValue().numval : 2; }
#elif GC_DEBUG
    { return optionTable.has(o_verbosity) ?
        optionTable[o_verbosity]->getValue().numval : 2; }
#else
    { return optionTable.has(o_verbosity) ?
        optionTable[o_verbosity]->getValue().numval : 0; }
#endif
  int          printSuccess() const
     { return optionTable.has(":print-success") ?
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
  int          sat_reduce_proof;             // Enable proof reduction
  int          sat_reorder_pivots;           // Enable pivots reordering for interpolation
  double       sat_ratio_red_time_solv_time; // Reduction time / solving time for each global loop
  double       sat_red_time;                 // Reduction time for each global loop
  int          sat_num_glob_trans_loops;     // Number of loops recycle pivots + reduction
  int          sat_remove_mixed;             // Compression of AB-mixed subtrees
  int              sat_propagate_small;                  // Try to propagate first smaller clauses
  int              sat_restart_learnt_thresh;    // Restart solver if the current learnt has width > thresh
  int              sat_orig_thresh;                              // Allows original clauses of width up to thresh
  // Proof manipulation parameters
  double       proof_ratio_red_solv;         // Ratio reduction time solving time for each global loop
  double       proof_red_time;               // Reduction time for each global loop
  int          proof_reorder_pivots;         // Enable pivot reordering
  int          proof_reduce_while_reordering;// Enable reduction during reordering
  int          proof_random_context_analysis;// Examine a context with 50% probability
  int          proof_random_swap_application;// Apply a chosen A1,A2,B2k rule with 50% probability
  int          proof_remove_mixed;           // Enable removal of mixed predicates
  int          proof_certify_inter;          // Check interpolants
  int          proof_random_seed;            // Randomly initialize seed for transformation
//   int                   proof_rec_piv;                                // Enable the use of RecyclePivots for reduction
//  int            proof_push_units;                    // Enable pushing down units heuristics
//  int          proof_struct_hash_build;                // Enable structural hashing while building the proof
//  int                    proof_struct_hash;                    // Enable structural hashing for compression
  int              proof_switch_to_rp_hash;              // Instead of hashing + rp does the opposite
//  int                    proof_transf_trav;                    // Enable transformation traversals
//  int            proof_check;                                  // Enable proof checking
//  int            proof_alternative_inter;              // Dual formula for AB pivots
//  int            proof_multiple_inter;                 // Multiple interpolants
//  int          proof_interpolant_cnf;          // Enable proof restructuring for interpolant in CNF
  int          proof_trans_strength;             // Light proof restructuring for stronger/weaker interpolants, for Pudlak/McMillan/McMillan' algorithms
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

  // interpolant parameters
  int           simplify_interpolant;

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
