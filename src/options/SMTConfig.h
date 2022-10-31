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

#include "SolverTypes.h"
#include "StringMap.h"
#include "smt2newcontext.h"
#include "smt2tokens.h"
#include "OsmtApiException.h"
#include "OsmtInternalException.h"
#include "ParseNodePrinter.h"

#include <cstring>
#include <fstream>
#include <iostream>
#include <libgen.h>
#include <list>
#include <memory>
#include <string>

enum class ASTType {
      CMD_T      , CMDL_T
    , SYM_T      , SYML_T
    , QSYM_T     , QSYML_T
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
    , UNDEF_T
};


class SMTOption {

public:
    ConstType type = ConstType::empty;
    std::variant<std::string, int, double, bool> value = 0;

    std::string toString() const {
        if (auto val = std::get_if<std::string>(&value)) {
            return *val;
        } else if (auto val = std::get_if<int>(&value)) {
            return std::to_string(*val);
        } else if (auto val = std::get_if<double>(&value)) {
            return std::to_string(*val);
        } else if (auto val =  std::get_if<bool>(&value)) {
            return *val ? "true" : "false";
        }
        assert(false);
        return {};
    }
    std::string getStringVal() const {
        if (type == ConstType::string) {
            auto val = std::get_if<std::string>(&value);
            assert(val);
            return *val;
        }
        else {
            throw OsmtApiException("Attempt to get string value of a non-string type");
        }
    }
    double getDoubleVal() const {
        if (type == ConstType::integral) {
            if (auto val = std::get_if<int>(&value)) {
                return static_cast<double>(*val);
            } else {
                throw OsmtInternalException("Inconsistent value for option");
            }
        } else if (type == ConstType::decimal) {
            auto val = std::get_if<double>(&value);
            assert(val);
            return *val;
        } else {
            throw OsmtApiException("Attempted to obtain double value for non-numeric type");
        }
    }
    int getIntVal() const {
        if (type == ConstType::integral) {
            auto val = std::get_if<int>(&value);
            assert(val);
            return *val;
        } else {
            throw OsmtApiException("Attempted to obtain int value for non-int type");
        }
    }
    bool getBoolVal() const {
        if (type == ConstType::boolean) {
            auto val = std::get_if<bool>(&value);
            assert(val);
            return *val;
        }
        else {
            throw OsmtApiException("Attempt to obtain boolean value for non-boolean type");
        }
    }
    SMTOption() = default;
    explicit SMTOption(bool i) : type(ConstType::boolean), value(i) {}
    explicit SMTOption(int i) : type(ConstType::integral), value(i) {}
    explicit SMTOption(double i) : type(ConstType::decimal), value(i) {}
    explicit SMTOption(std::string && s) : type(ConstType::string), value(std::move(s)) {}
    explicit SMTOption(AttributeValueNode const & n) {
        if (auto specConst_p = std::get_if<std::unique_ptr<SpecConstNode>>(&n.value)) {
            auto const & specConst = (**specConst_p);
            type = specConst.type;
            switch (type) {
            case ConstType::integral: {
                value = std::stoi(*specConst.value);
                break;
            }
            case ConstType::boolean: {
                value = *specConst.value == "true";
                break;
            }
            case ConstType::string: {
                value = *specConst.value;
                break;
            }
            case ConstType::decimal: {
                value = std::stod(*specConst.value);
                break;
            }
            case ConstType::binary: {
                value = std::stoi(static_cast<std::string const>(std::string_view(&(*specConst.value)[2], (*specConst.value).size()-2)), nullptr, 2);
                break;
            }
            case ConstType::hexadecimal: {
                value = std::stoi(static_cast<std::string const>(std::string_view(&(*specConst.value)[2], (*specConst.value).size()-2)), nullptr, 16);
                break;
            }
            case ConstType::sexpr:
            case ConstType::symbol: {
                value = *specConst.value;
                break;
            }
            case ConstType::empty: {
                throw OsmtInternalException("Parsed an empty type");
            }
            }
        } else if (auto symbol_p = std::get_if<std::unique_ptr<SymbolNode>>(&n.value)) {
            auto const & symbol = (**symbol_p);
            std::string symbolString = opensmt::nodeToString()(symbol);
            if (not symbol.quoted and symbolString == "true") {
                type = ConstType::boolean;
                value = true;
            } else if (not symbol.quoted and symbolString == "false") {
                type = ConstType::boolean;
                value = false;
            } else {
                type = symbol.getType();
                value = std::move(symbolString);
            }
        } else if (auto sexprVec_p = std::get_if<std::unique_ptr<std::vector<SExpr*>>>(&n.value)) {
            assert(sexprVec_p);
            type = ConstType::sexpr;
            auto const & sexprVec = **sexprVec_p;
            auto str = std::accumulate(sexprVec.begin(), sexprVec.end(), std::string{},
                            [](std::string & a, SExpr const * b) {
                                return a += (a.empty() ? "" : " ") + opensmt::nodeToString()(b);
                            });
            value = "(" + str + ")";
        }
    }
    inline bool isEmpty() const { return type == ConstType::empty; }
};

// Type safe wrapper for split types
typedef struct SpType    { int t; } SpType;
typedef struct SpPref    { int t; } SpPref;

typedef struct SpFormat  { int t; } SpFormat;

enum class ItpAlgorithm {
    itp_alg_mcmillan, itp_alg_pudlak, itp_alg_mcmillanp,
    itp_alg_ps, itp_alg_psw, itp_alg_pss, itp_euf_alg_strong,
    itp_euf_alg_weak, itp_euf_alg_random, itp_lra_alg_strong,
    itp_lra_alg_weak, itp_lra_alg_factor, itp_lra_alg_decomposing_strong,
    itp_lra_alg_decomposing_weak};

static const std::string itp_lra_factor_0 = "1/2";

inline bool operator==(const SpType& s1, const SpType& s2) { return s1.t == s2.t; }
inline bool operator!=(const SpType& s1, const SpType& s2) { return s1.t != s2.t; }
inline bool operator==(const SpPref& s1, const SpPref& s2) { return s1.t == s2.t; }
inline bool operator!=(const SpPref& s1, const SpPref& s2) { return s1.t != s2.t; }
inline bool operator==(const SpFormat& s1, const SpFormat& s2) { return s1.t == s2.t; }
inline bool operator!=(const SpFormat& s1, const SpFormat& s2) { return s1.t != s2.t; }

static const char* const spts_lookahead = "lookahead";
static const char* const spts_scatter   = "scattering";
static const char* const spts_none      = "none";

static const char* const spts_search_counter = "search_counter";
static const char* const spts_time      = "time";

static const char* const spprefs_tterm   = "tterm";
static const char* const spprefs_blind   = "blind";
static const char* const spprefs_bterm   = "bterm";
static const char* const spprefs_rand    = "random";
static const char* const spprefs_noteq   = "noteq";
static const char* const spprefs_eq   = "eq";
static const char* const spprefs_tterm_neq   = "tterm_neq";

static const char* const spformats_brief  = "brief";
static const char* const spformats_full   = "full";

static const struct SpType spt_none      = { 0 };
static const struct SpType spt_lookahead = { 1 };
static const struct SpType spt_scatter   = { 2 };

enum class SpUnit : char { search_counter, time };

static const struct SpPref sppref_tterm = { 0 };
static const struct SpPref sppref_blind = { 1 };
static const struct SpPref sppref_bterm = { 2 };
static const struct SpPref sppref_rand  = { 3 };
static const struct SpPref sppref_undef = { 4 };
static const struct SpPref sppref_noteq = { 5 };
static const struct SpPref sppref_eq = { 6 };
static const struct SpPref sppref_tterm_neq = { 7 };

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
  static const char* o_rnd_pol;
  static const char* o_rnd_init_act;
  static const char* o_garbage_frac;
  static const char* o_restart_first;
  static const char* o_restart_inc;
  static const char* o_produce_proofs;
  static const char* o_produce_inter;
  static const char* o_certify_inter;
  static const char* o_simplify_inter;
  static const char* o_interpolant_cnf;
  static const char* o_proof_struct_hash;
  static const char* o_proof_num_graph_traversals;
  static const char* o_proof_red_trans;
  static const char* o_proof_rec_piv;
  static const char* o_proof_push_units;
  static const char* o_proof_transf_trav;
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
  static const char* o_sat_scatter_split;
  static const char* o_sat_lookahead_split;
  static const char* o_sat_pure_lookahead;
  static const char* o_lookahead_score_deep;
  static const char* o_sat_split_units;
  static const char* o_sat_split_preference;
  static const char* o_sat_split_test_cube_and_conquer;
  static const char* o_sat_split_randomize_lookahead;
  static const char* o_sat_split_randomize_lookahead_buf;
  static const char* o_produce_models;
  static const char* o_sat_remove_symmetries;
  static const char* o_dryrun;
  static const char* o_do_substitutions;
  static const char* o_respect_logic_partitioning_hints;
  static const char* o_output_dir;
  static const char* o_ghost_vars;
  static const char* o_sat_solver_limit;
  static const char* o_global_declarations;

  static const char* o_sat_split_mode;
private:

  static const char* s_err_not_str;
  static const char* s_err_not_bool;
  static const char* s_err_not_num;
  static const char* s_err_seed_zero;
  static const char* s_err_unknown_split;
  static const char* s_err_unknown_units;

  SMTOption        option_Empty;
  std::vector<std::string> option_names;
  std::unordered_map<std::string,SMTOption> infoTable;
  std::unordered_map<std::string,SMTOption> optionTable;

  bool usedForInitialization = false; // Some options can be changed only before this config is used for initialization of MainSolver
  bool isPreInitializationOption(std::string const & o_name) {
      return o_name == o_produce_inter or o_name == o_produce_proofs
        or o_name == o_sat_pure_lookahead or o_name == o_sat_lookahead_split
        or o_name == o_sat_scatter_split or o_name == o_ghost_vars;
  }

  void          insertOption(std::string const & o_name, SMTOption && o) {
      if (optionTable.find(o_name) != optionTable.end()) optionTable.insert({o_name, std::move(o)});
      else {
          option_names.push_back(o_name);
          optionTable.insert({o_name, std::move(o)});
      }
  }
  std::string append_output_dir(std::string const & name) const
  {
      std::string path = output_dir();
      // If output_dir() is not defined (or is empty), just return (copy of) name
      if (path.empty()) {
          return name;
      } else {
          return path + '/' + name;
      }
  }
  //
  // For standard executable
  //
public:
    //
    // For API
    //
    SMTConfig () {
        initializeConfig( );
    }

  void setOption(std::string const & name, SMTOption const & value);
  const SMTOption& getOption(std::string const & name) const;

  bool setInfo(std::string && name, SMTOption && value);
  SMTOption getInfo(std::string const & name) const;

  void initializeConfig ( );

  void parseConfig      ( char * );
  void parseCMDLine     ( int argc, char * argv[ ] );
  void printHelp        ( );
  void printConfig      ( std::ostream & out );

  inline int  getRandomSeed   ( ) const { return optionTable.find(o_random_seed) != optionTable.end() ? optionTable.at(o_random_seed).getIntVal(): 91648253; }
  inline void setProduceModels( ) { insertOption(o_produce_models, SMTOption(1)); }
  inline bool setRandomSeed(int seed) { insertOption(o_random_seed, SMTOption(seed)); return true; }

  void setUsedForInitiliazation() { usedForInitialization = true; }

  inline bool produceProof( ) {
      return optionTable.find(o_produce_proofs) != optionTable.end() ? optionTable[o_produce_proofs].getBoolVal() : false;
  }

  void setTimeQueries() { insertOption(o_time_queries, SMTOption(1)); }
  bool timeQueries()    { return optionTable.find(o_time_queries) != optionTable.end() ? optionTable[o_time_queries].getBoolVal() : false; }
  // Set reduction params
  inline void setReduction(bool r) { insertOption(o_proof_reduce, SMTOption(r)); }

  inline void setReductionGraph(int r) { insertOption(o_proof_num_graph_traversals, SMTOption(r)); }

  inline void setReductionLoops(int r) { insertOption(o_proof_red_trans, SMTOption(r)); }

  // Set interpolation algorithms
  inline void setBooleanInterpolationAlgorithm( ItpAlgorithm i ) { 
      insertOption(o_itp_bool_alg, SMTOption(static_cast<int>(i))); }

  inline void setEUFInterpolationAlgorithm( ItpAlgorithm i ) { insertOption(o_itp_euf_alg, SMTOption(static_cast<int>(i))); }

  inline void setLRAInterpolationAlgorithm( ItpAlgorithm i ) { insertOption(o_itp_lra_alg, SMTOption(static_cast<int>(i))); }

  inline void setLRAStrengthFactor(const char *factor) { insertOption(o_itp_lra_factor, SMTOption(factor)); }

  inline void setInstanceName(const char* name) { insertOption(o_inst_name, SMTOption(name)); }

  // Get interpolation algorithms
  inline ItpAlgorithm getBooleanInterpolationAlgorithm() const {
      return optionTable.find(o_itp_bool_alg) != optionTable.end() ? static_cast<ItpAlgorithm>(optionTable.at(o_itp_bool_alg).getIntVal())
                                                                   : ItpAlgorithm::itp_alg_mcmillan;
  }
  inline ItpAlgorithm getEUFInterpolationAlgorithm() const {
      return optionTable.find(o_itp_euf_alg) != optionTable.end() ? static_cast<ItpAlgorithm>(optionTable.at(o_itp_euf_alg).getIntVal())
                                                                  : ItpAlgorithm::itp_euf_alg_strong;
  }

  inline ItpAlgorithm getLRAInterpolationAlgorithm() const {
      return optionTable.find(o_itp_lra_alg) != optionTable.end() ? static_cast<ItpAlgorithm>(optionTable.at(o_itp_lra_alg).getIntVal())
                                                                  : ItpAlgorithm::itp_lra_alg_strong;
  }

  inline std::string getLRAStrengthFactor() const {
      return optionTable.find(o_itp_lra_factor) != optionTable.end() ? optionTable.at(
              o_itp_lra_factor).getStringVal() : itp_lra_factor_0;
  }


  inline std::string getInstanceName() const {
      return optionTable.find(o_inst_name) != optionTable.end() ? optionTable.at(o_inst_name).getStringVal() : "unknown";
  }

  lbool        status;                       // Status of the benchmark
//  int          incremental;                  // Incremental solving
  bool isIncremental() const {
      return optionTable.find(o_incremental) != optionTable.end() ?
             optionTable.at(o_incremental).getBoolVal() : true;
  }
  bool produce_models() const {
      return optionTable.find(o_produce_models) != optionTable.end() ?
              optionTable.at(o_produce_models).getBoolVal() : true;
  }
  bool produceStats() const {
      return optionTable.find(o_produce_stats) != optionTable.end() &&
             optionTable.at(o_produce_stats).getBoolVal(); }
  std::string  getStatsOut() const {
      return optionTable.find(o_stats_out) != optionTable.end() ? optionTable.at(o_stats_out).getStringVal() : "/dev/stdout";
  }

  int sat_grow() const
    { return optionTable.find(o_grow) != optionTable.end() ?
        optionTable.at(o_grow).getBoolVal() : 0; }
  int sat_clause_lim() const
    { return optionTable.find(o_clause_lim) != optionTable.end() ?
        optionTable.at(o_clause_lim).getIntVal() : 20; }
  int sat_subsumption_lim() const
    { return optionTable.find(o_subsumption_lim) != optionTable.end() ?
        optionTable.at(o_subsumption_lim).getIntVal() : 1000; }
  double sat_simp_garbage_frac() const
    { return optionTable.find(o_simp_garbage_frac) != optionTable.end() ?
        optionTable.at(o_simp_garbage_frac).getDoubleVal() : 0.5; }
  int sat_use_asymm() const
    { return optionTable.find(o_use_asymm) != optionTable.end() ?
        optionTable.at(o_use_asymm).getBoolVal() : false; }
  int sat_use_rcheck() const {
      return optionTable.find(o_use_rcheck) != optionTable.end() ?
             optionTable.at(o_use_rcheck).getBoolVal() : false;
  }
  int sat_use_elim() const {
      return optionTable.find(o_use_elim) != optionTable.end() ?
             optionTable.at(o_use_elim).getBoolVal() : true;
  }
  double sat_var_decay() const {
      return optionTable.find(o_var_decay) != optionTable.end() ?
             optionTable.at(o_var_decay).getDoubleVal() : 1 / 0.95; }
  double sat_clause_decay() const {
      return optionTable.find(o_clause_decay) != optionTable.end() ?
             optionTable.at(o_clause_decay).getDoubleVal() : 1 / 0.999; }
  double sat_random_var_freq() const {
      return optionTable.find(o_random_var_freq) != optionTable.end() ?
             optionTable.at(o_random_var_freq).getDoubleVal() : 0.02; }
  uint32_t sat_random_seed() const {
      return optionTable.find(o_random_seed) != optionTable.end() ?
             optionTable.at(o_random_seed).getIntVal() : 91648253; }
  bool sat_luby_restart() const {
      return optionTable.find(o_luby_restart) != optionTable.end() ?
             optionTable.at(o_luby_restart).getBoolVal() : true;
  }
  uint32_t sat_ccmin_mode() const {
      return optionTable.find(o_ccmin_mode) != optionTable.end() ?
             optionTable.at(o_ccmin_mode).getIntVal() : 2;
  }
  bool sat_rnd_pol() const {
      return optionTable.find(o_rnd_pol) != optionTable.end() ?
             optionTable.at(o_rnd_pol).getBoolVal() : false;
  }
  bool sat_rnd_init_act() const {
      return optionTable.find(o_rnd_init_act) != optionTable.end() ?
             optionTable.at(o_rnd_init_act).getBoolVal() : false; }
  double sat_garbage_frac() const {
      return optionTable.find(o_garbage_frac) != optionTable.end() ?
             optionTable.at(o_garbage_frac).getDoubleVal() : 0.20;
  }
  uint32_t sat_restart_first() const {
      return optionTable.find(o_restart_first) != optionTable.end() ?
             optionTable.at(o_restart_first).getIntVal() : 100; }
  double sat_restart_inc() const {
      return optionTable.find(o_restart_inc) != optionTable.end() ?
             optionTable.at(o_restart_inc).getDoubleVal() : 1.1;
  }
  int proof_interpolant_cnf() const {
      return optionTable.find(o_interpolant_cnf) != optionTable.end() ?
             optionTable.at(o_interpolant_cnf).getBoolVal() : false;
  }
  int certify_inter() const {
      return optionTable.find(o_certify_inter) != optionTable.end() ?
             optionTable.at(o_certify_inter).getBoolVal(): false;
  }
  bool produce_inter() const {
      return optionTable.find(o_produce_inter) != optionTable.end() ?
             optionTable.at(o_produce_inter).getBoolVal() : false;
  }
  uint32_t simplify_inter() const {
      return optionTable.find(o_simplify_inter) != optionTable.end() ?
             optionTable.at(o_simplify_inter).getIntVal() : false;
  }
  bool proof_struct_hash() const {
      return optionTable.find(o_proof_struct_hash) != optionTable.end() ?
             optionTable.at(o_proof_struct_hash).getBoolVal() : true;
  }
  uint32_t proof_num_graph_traversals() const {
      return optionTable.find(o_proof_num_graph_traversals) != optionTable.end() ?
             optionTable.at(o_proof_num_graph_traversals).getIntVal() : 3; }
  uint32_t proof_red_trans() const {
      return optionTable.find(o_proof_red_trans) != optionTable.end() ?
             optionTable.at(o_proof_red_trans).getIntVal() : 2;
  }
  bool proof_rec_piv() const {
      return optionTable.find(o_proof_rec_piv) != optionTable.end() ?
             optionTable.at(o_proof_rec_piv).getBoolVal() : true;
  }
  bool proof_push_units() const {
      return optionTable.find(o_proof_push_units) != optionTable.end() ?
             optionTable.at(o_proof_push_units).getBoolVal() : true;
  }
  bool proof_transf_trav() const {
      return optionTable.find(o_proof_transf_trav) != optionTable.end() ?
             optionTable.at(o_proof_transf_trav).getBoolVal() : true;
  }
  bool proof_check() const {
      return optionTable.find(o_proof_check) != optionTable.end() ?
             optionTable.at(o_proof_check).getBoolVal() : true;
  }
  bool proof_multiple_inter() const {
      return optionTable.find(o_proof_multiple_inter) != optionTable.end() ?
             optionTable.at(o_proof_multiple_inter).getBoolVal() : true;
  }
  bool proof_alternative_inter() const {
      return optionTable.find(o_proof_alternative_inter) != optionTable.end() ?
             optionTable.at(o_proof_alternative_inter).getBoolVal() : false;
  }
  bool proof_reduce() const {
      return optionTable.find(o_proof_reduce) != optionTable.end() ?
             optionTable.at(o_proof_reduce).getBoolVal() : false;
  }
  uint32_t itp_bool_alg() const {
      return optionTable.find(o_itp_bool_alg) != optionTable.end() ?
             optionTable.at(o_itp_bool_alg).getIntVal() : 0;
  }
  uint32_t itp_euf_alg() const
    { return optionTable.find(o_itp_euf_alg) != optionTable.end() ?
        optionTable.at(o_itp_euf_alg).getIntVal() : 0;
  }
  uint32_t itp_lra_alg() const {
      return optionTable.find(o_itp_lra_alg) != optionTable.end() ?
        optionTable.at(o_itp_lra_alg).getIntVal() : 0; }
  uint32_t sat_dump_rnd_inter() const {
      return optionTable.find(o_sat_dump_rnd_inter) != optionTable.end() ?
             optionTable.at(o_sat_dump_rnd_inter).getIntVal() : 2; }

    bool declarations_are_global() const {
      return optionTable.find(o_global_declarations) != optionTable.end() ?
             optionTable.at(o_global_declarations).getBoolVal() : false;
  }

  SpUnit sat_resource_units() const {
      if (optionTable.find(o_sat_resource_units) != optionTable.end()) {
          std::string type = optionTable.at(o_sat_resource_units).getStringVal();
          if (type == spts_search_counter) {
              return SpUnit::search_counter;
          } else if (type == spts_time) {
              return SpUnit::time;
          }
      }
      return SpUnit::search_counter;
    }

  bool respect_logic_partitioning_hints() const {
      return optionTable.find(o_respect_logic_partitioning_hints) != optionTable.end() ?
             optionTable.at(o_respect_logic_partitioning_hints).getBoolVal() : false;
  }
  double sat_resource_limit() const {
      return optionTable.find(o_sat_resource_limit) != optionTable.end() ?
             optionTable.at(o_sat_resource_limit).getDoubleVal() : -1;
  }

  std::string dump_state() const {
      if (optionTable.find(o_dump_state) != optionTable.end()) {
          return append_output_dir(optionTable.at(o_dump_state).getStringVal());
      } else {
          std::string name = getInstanceName();
          return name.substr(0, name.size() - strlen(".smt2"));
      }
  }
  std::string output_dir() const {
      return optionTable.find(o_output_dir) != optionTable.end() ? optionTable.at(o_output_dir).getStringVal() : "";
  }
  bool dump_only() const {
      return optionTable.find(o_dump_only) != optionTable.end() ? optionTable.at(o_dump_only).getBoolVal(): false;
  }
  bool dump_query() const {
      return optionTable.find(o_dump_query) != optionTable.end() ? optionTable.at(o_dump_query).getBoolVal() : false;
  }

  void set_dump_query_name(std::string && dump_query_name) {
        if (optionTable.find(o_dump_query_name) != optionTable.end()) {
            optionTable.insert({o_dump_query_name, SMTOption(std::move(dump_query_name))});
        } else {
            insertOption(o_dump_query_name, SMTOption(std::move(dump_query_name)));
        }
  }


  std::string dump_query_name() const {
      return optionTable.find(o_dump_query_name) != optionTable.end() ?
             append_output_dir(optionTable.at(o_dump_query_name).getStringVal()) : "";
  }

  bool sat_dump_learnts() const {
      return optionTable.find(o_sat_dump_learnts) != optionTable.end() ?
             optionTable.at(o_sat_dump_learnts).getBoolVal() : false; }

  bool sat_split_test_cube_and_conquer() const {
      return optionTable.find(o_sat_split_test_cube_and_conquer) != optionTable.end() ?
             optionTable.at(o_sat_split_test_cube_and_conquer).getBoolVal() : false;
  }

  SpType sat_split_type() const {
      if (sat_lookahead_split()) {
          return spt_lookahead;
      } else if (sat_scatter_split()) {
          return spt_scatter;
      } else {
          return spt_none;
      }
  }

  SpUnit sat_split_units() const {
      if (optionTable.find(o_sat_split_units) != optionTable.end()) {
          std::string type = optionTable.at(o_sat_split_units).getStringVal();
          if (type == spts_search_counter) {
              return SpUnit::search_counter;
          } else if (type == spts_time) {
              return SpUnit::time;
          }
      }
      return SpUnit::search_counter;
  }

  double sat_split_inittune() const {
      return optionTable.find(o_sat_split_inittune) != optionTable.end() ?
             optionTable.at(o_sat_split_inittune).getDoubleVal() :
              -1;
  }
  double sat_split_midtune() const {
      return optionTable.find(o_sat_split_midtune) != optionTable.end() ?
              optionTable.at(o_sat_split_midtune).getDoubleVal() :
              -1;
  }
  uint32_t sat_split_num() const {
      return optionTable.find(o_sat_split_num) != optionTable.end() ?
              optionTable.at(o_sat_split_num).getIntVal() :
              2;
  }
  int sat_split_fixvars() const {
      return optionTable.find(o_sat_split_fix_vars) != optionTable.end() ?
              optionTable.at(o_sat_split_fix_vars).getIntVal() :
              -1;
  }
  bool sat_split_asap() const {
      return optionTable.find(o_sat_split_asap) != optionTable.end() ?
             optionTable.at(o_sat_split_asap).getBoolVal():
             false;
  }
  bool sat_lookahead_split() const {
      return optionTable.find(o_sat_lookahead_split) != optionTable.end() ?
             optionTable.at(o_sat_lookahead_split).getBoolVal():
             false;
  }
  bool sat_scatter_split() const {
      return optionTable.find(o_sat_scatter_split) != optionTable.end() ?
             optionTable.at(o_sat_scatter_split).getBoolVal() :
             false;
  }
  bool sat_pure_lookahead() const {
      return optionTable.find(o_sat_pure_lookahead) != optionTable.end() ?
              optionTable.at(o_sat_pure_lookahead).getBoolVal() :
              false;
  }
  bool lookahead_score_deep() const {
      return optionTable.find(o_lookahead_score_deep) != optionTable.end() ?
              optionTable.at(o_lookahead_score_deep).getBoolVal() :
              false;
  }
  bool randomize_lookahead() const {
      return optionTable.find(o_sat_split_randomize_lookahead) != optionTable.end() ?
              optionTable.at(o_sat_split_randomize_lookahead).getBoolVal() :
              false;
  }

  uint32_t randomize_lookahead_bufsz() const {
      return optionTable.find(o_sat_split_randomize_lookahead_buf) != optionTable.end() ?
              optionTable.at(o_sat_split_randomize_lookahead_buf).getIntVal() :
              true;
  }

  bool remove_symmetries() const {
      return optionTable.find(o_sat_remove_symmetries) != optionTable.end() ?
             optionTable.at(o_sat_remove_symmetries).getBoolVal() : false; }

  bool dryrun() const {
      return optionTable.find(o_dryrun) != optionTable.end() ?
             optionTable.at(o_dryrun).getBoolVal() : false; }

  void set_dryrun(bool b) { insertOption(o_dryrun, SMTOption(b)); }

  SpPref sat_split_preference() const {
    if (optionTable.find(o_sat_split_preference) != optionTable.end()) {
        std::string type = optionTable.at(o_sat_split_preference).getStringVal();
        if (type == spprefs_tterm) return sppref_tterm;
        if (type == spprefs_blind) return sppref_blind;
        if (type == spprefs_bterm) return sppref_bterm;
        if (type == spprefs_rand) return sppref_rand;
        if (type == spprefs_noteq) return sppref_noteq;
        if (type == spprefs_eq) return sppref_eq;
        if (type == spprefs_tterm_neq) return sppref_tterm_neq;
    }
    return sppref_blind;
  }

  bool use_ghost_vars() const {
      return optionTable.find(o_ghost_vars) != optionTable.end() ?
             optionTable.at(o_ghost_vars).getBoolVal() :
             false;
  }

  bool do_substitutions() const {
      return optionTable.find(o_do_substitutions) != optionTable.end()?
             optionTable.at(o_do_substitutions).getBoolVal() : true; }


   bool use_theory_polarity_suggestion() const { return sat_theory_polarity_suggestion != 0; }

   uint32_t sat_solver_limit() const {
       return optionTable.find(o_sat_solver_limit) != optionTable.end() ?
              optionTable.at(o_sat_solver_limit).getIntVal() : 0; }

    bool sat_split_mode() const {
        return optionTable.find(o_sat_split_mode) != optionTable.end() ?
               optionTable.at(o_sat_split_mode).getBoolVal() :
               false;
    }

//  int          produce_stats;                // Should print statistics ?
  int          print_stats;                  // Should print statistics ?
  int          print_proofs_smtlib2;         // Should print proofs ?
  int          print_proofs_dotty;           // Should print proofs ?
  bool         rocset;                       // Regular Output Channel set ?
  bool         docset;                       // Diagnostic Output Channel set ?
  int          dump_formula;                 // Dump input formula
  uint32_t verbosity() const {           // Verbosity level
        return optionTable.find(o_verbosity) != optionTable.end() ?
               optionTable.at(o_verbosity).getIntVal() : 0;
  }
  bool printSuccess() const {
      return optionTable.find(":print-success") != optionTable.end() ?
             optionTable.at(":print-success").getBoolVal() : false;
  }
  int          certification_level;          // Level of certification
  char         certifying_solver[256];       // Executable used for certification

  // SAT-Solver related parameters
  int          sat_theory_polarity_suggestion;  // Should the SAT solver ask the theory solver for var polarity when making a decision
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
  // CUF-Solver related parameter
  int          cuf_bitwidth;                  // Bit-width to use by the CUF solver
  // BV-Solver related parameters
  int          bv_disable;                   // Disable the solver
  // DL-Solver related parameters
  int          dl_disable;                   // Disable the solver
  // LRA-Solver related parameters
  int          lra_disable;                  // Disable the solver
  int          lra_poly_deduct_size;         // Used to define the size of polynomial to be used for deduction; 0 - no deduction for polynomials
  int          lra_trade_off;                // Trade-off value for DL preprocessing
  int          lra_integer_solver;           // Flag to require integer solution for LA problem
  int          lra_check_on_assert;          // Probability (0 to 100) to run check when assert is called

    static char* server_host;
    static uint16_t server_port;
    static char* database_host;
    static uint16_t database_port;

    void setSimplifyInterpolant(int val) {
        setOption(o_simplify_inter, SMTOption(val));
    }

    int getSimplifyInterpolant() const {
        return simplify_inter();
    }

private:

  std::ofstream     stats_out;                    // File for statistics
  std::ofstream     out;                          // Regular output channel
  std::ofstream     err;                          // Diagnostic output channel
};
#endif
