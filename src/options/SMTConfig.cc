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

#include "SMTConfig.h"

#include "OsmtInternalException.h"

#include <sstream>

//---------------------------------------------------------------------------------
// SMTConfig

void SMTConfig::setOption(std::string const & name, const SMTOption& value) {
    if (usedForInitialization && isPreInitializationOption(name)) {
        throw OsmtApiException("Option cannot be changed at this point");
    }
    // Special options:
    // stats_out
    if (name == o_stats_out) {
        if (value.type != ConstType::string) { throw OsmtApiException(s_err_not_str); }
        if (optionTable.find(name) == optionTable.end())
            stats_out.open(value.getStringVal(), std::ios_base::out);
        else if (optionTable[name].getStringVal() != value.getStringVal()) {
            if (stats_out.is_open()) {
                stats_out.close();
                stats_out.open(value.getStringVal(), std::ios_base::out);
            }
        }
        else {}
    }

    // produce stats
    if (name == o_produce_stats) {
        if (value.type != ConstType::boolean) {
            throw OsmtApiException(s_err_not_bool);
        } else if (value.getBoolVal()) {
            // Gets set to true
            if (optionTable.find(o_stats_out) == optionTable.end()) {
                if (optionTable.find(o_produce_stats) == optionTable.end() || not optionTable[o_produce_stats].getBoolVal()) {
                    // Insert the default value
                    insertOption(o_stats_out, SMTOption("/dev/stdout"));
                } else if (optionTable.find(o_produce_stats) != optionTable.end() and optionTable[o_produce_stats].getBoolVal()) {
                    assert(false);
                }
            }
            else { } // No action required

            if (!stats_out.is_open()) stats_out.open(optionTable[o_stats_out].getStringVal(), std::ios_base::out);
        }
        else if (optionTable.find(o_produce_stats) != optionTable.end() && optionTable[o_produce_stats].getBoolVal()) {
            // gets set to false and was previously true
            if (optionTable.find(o_stats_out) != optionTable.end()) {
                stats_out.close();
            }
        }
    }

    if (name == o_random_seed) {
        if (value.type != ConstType::numeral) {
            throw OsmtApiException(s_err_not_num);
        }
        uint32_t seed = value.getUint32Val();
        if (seed == 0) { throw OsmtApiException(s_err_seed_zero); }
    }

    if (name == o_sat_split_type) {
        if (value.type != ConstType::string) { throw OsmtApiException(s_err_not_str); }
        std::string val = value.getStringVal();
        if (val != spts_lookahead && val != spts_scatter && val != spts_none) {
            throw OsmtApiException(s_err_unknown_split);
        }
    }
    if (name == o_sat_split_units) {
        if (value.type != ConstType::string) { throw OsmtApiException(s_err_not_str); }
        std::string val = value.getStringVal();
        if (val != spts_time && val != spts_search_counter) {
            throw OsmtApiException(s_err_unknown_units);
        }
    }
    auto itr = optionTable.find(name);
    if (itr != optionTable.end()) {
        optionTable.erase(itr);
    }
    insertOption(name, SMTOption(value));
}

const SMTOption& SMTConfig::getOption(std::string const & name) const {
    auto itr = optionTable.find(name);
    if (itr != optionTable.end())
        return itr->second;
    else
        return option_Empty;
}

bool SMTConfig::setInfo(std::string && name_, SMTOption && value) {
    if (infoTable.find(name_) != infoTable.end())
        infoTable.erase(infoTable.find(name_));
    infoTable.insert({name_, value});
    return true;
}

SMTOption SMTConfig::getInfo(std::string const & name) const {
    if (infoTable.find(name) != infoTable.end())
        return infoTable.at(name);
    else
        return {};
}

const char* SMTConfig::o_produce_models = ":produce-models";
const char* SMTConfig::o_verbosity      = ":verbosity";
const char* SMTConfig::o_incremental    = ":incremental";
const char* SMTConfig::o_produce_stats  = ":produce-stats";
const char* SMTConfig::o_stats_out      = ":stats-out";
const char* SMTConfig::o_random_seed    = ":random-seed";
const char* SMTConfig::o_grow           = ":grow";
const char* SMTConfig::o_clause_lim     = ":cl-lim";
const char* SMTConfig::o_subsumption_lim = ":sub-lim";
const char* SMTConfig::o_simp_garbage_frac = ":simp-gc-frac";
const char* SMTConfig::o_use_asymm     = ":asymm";
const char* SMTConfig::o_use_rcheck    = ":rcheck";
const char* SMTConfig::o_use_elim      = ":elim";
const char* SMTConfig::o_var_decay     = ":var-decay";
const char* SMTConfig::o_clause_decay  = ":clause-decay";
const char* SMTConfig::o_random_var_freq= ":random-var-freq";
const char* SMTConfig::o_luby_restart  = ":luby-restart";
const char* SMTConfig::o_ccmin_mode    = ":ccmin-mode";
const char* SMTConfig::o_rnd_pol       = ":rnd-pol";
const char* SMTConfig::o_rnd_init_act  = ":rnd-init-act";
const char* SMTConfig::o_sat_dump_rnd_inter = ":sat-num-rnd-itps";
const char* SMTConfig::o_garbage_frac  = ":garbage-frac";
const char* SMTConfig::o_restart_first = ":restart-first";
const char* SMTConfig::o_restart_inc   = ":restart-inc";
const char* SMTConfig::o_produce_proofs = ":produce-proofs";
const char* SMTConfig::o_produce_inter = ":produce-interpolants";
const char* SMTConfig::o_certify_inter = ":certify-interpolants";
const char* SMTConfig::o_simplify_inter = ":simplify-interpolants";
const char* SMTConfig::o_interpolant_cnf = ":cnf-interpolants";
const char* SMTConfig::o_proof_struct_hash       = ":proof-struct-hash";
const char* SMTConfig::o_proof_check   = ":proof-check";
const char* SMTConfig::o_proof_multiple_inter    = ":proof-interpolation-property";
const char* SMTConfig::o_proof_alternative_inter = ":proof-alternative-inter";
const char* SMTConfig::o_proof_reduce  = ":proof-reduce";
const char* SMTConfig::o_proof_rec_piv = ":proof-rpi";
const char* SMTConfig::o_proof_push_units = ":proof-lower-units";
const char* SMTConfig::o_proof_transf_trav = ":proof-reduce-expose";
const char* SMTConfig::o_proof_num_graph_traversals = ":proof-num-graph-traversals";
const char* SMTConfig::o_proof_red_trans = ":proof-num-global-iterations";
const char* SMTConfig::o_itp_bool_alg = ":interpolation-bool-algorithm";
const char* SMTConfig::o_itp_euf_alg = ":interpolation-euf-algorithm";
const char* SMTConfig::o_itp_lra_alg = ":interpolation-lra-algorithm";
const char* SMTConfig::o_itp_lra_factor = ":interpolation-lra-factor";
const char* SMTConfig::o_sat_resource_units = ":resource-units";
const char* SMTConfig::o_sat_resource_limit = ":resource-limit";
const char* SMTConfig::o_dump_state = ":dump-state";
const char* SMTConfig::o_time_queries = ":time-queries";
const char* SMTConfig::o_output_dir = ":output-dir";
const char* SMTConfig::o_ghost_vars = ":ghost-vars";
const char* SMTConfig::o_dump_query = ":dump-query";
const char* SMTConfig::o_dump_query_name = ":dump-query-name";
const char* SMTConfig::o_inst_name = ":instance-name";
const char* SMTConfig::o_dump_only = ":dump-only";
const char* SMTConfig::o_sat_dump_learnts = ":dump-learnts";
const char* SMTConfig::o_sat_split_type = ":split-type";
const char* SMTConfig::o_sat_split_inittune = ":split-init-tune";
const char* SMTConfig::o_sat_split_midtune = ":split-mid-tune";
const char* SMTConfig::o_sat_split_num = ":split-num";
const char* SMTConfig::o_sat_split_fix_vars = ":split-fix-vars";
const char* SMTConfig::o_sat_split_asap = ":split-asap";
const char* SMTConfig::o_sat_split_units = ":split-units";
const char* SMTConfig::o_sat_split_preference = ":split-preference";
const char* SMTConfig::o_sat_split_test_cube_and_conquer = ":test-cube-and-conquer";
const char* SMTConfig::o_sat_split_randomize_lookahead = ":randomize-lookahead";
const char* SMTConfig::o_sat_split_randomize_lookahead_buf = ":randomize-lookahead-buf"; // The n best found literals
const char* SMTConfig::o_sat_remove_symmetries = ":remove-symmetries";
const char* SMTConfig::o_dryrun = ":dryrun";
const char* SMTConfig::o_do_substitutions = ":do-substitutions";
const char* SMTConfig::o_respect_logic_partitioning_hints = ":respect-logic-partitioning-hints"; // Logic can have a say whether a var is good for partitioning
const char* SMTConfig::o_sat_scatter_split = ":scatter-split";
const char* SMTConfig::o_sat_lookahead_split = ":lookahead-split";
const char* SMTConfig::o_sat_pure_lookahead = ":pure-lookahead";
const char* SMTConfig::o_lookahead_score_deep = ":lookahead-score-deep";
const char* SMTConfig::o_sat_solver_limit = ":solver-limit";
const char* SMTConfig::o_global_declarations = ":global-declarations";
const char* SMTConfig::o_sat_split_mode     = ":split-mode";

char* SMTConfig::server_host=NULL;
uint16_t SMTConfig::server_port = 0;
char* SMTConfig::database_host=NULL;
uint16_t SMTConfig::database_port = 0;

// Error strings
const char* SMTConfig::s_err_not_str = "expected string";
const char* SMTConfig::s_err_not_bool = "expected Boolean";
const char* SMTConfig::s_err_not_num = "expected number";
const char* SMTConfig::s_err_seed_zero = "seed cannot be 0";
const char* SMTConfig::s_err_unknown_split = "unknown split type";
const char* SMTConfig::s_err_unknown_units = "unknown split units";

void
SMTConfig::initializeConfig( )
{
  // Set Global Default configuration
  status                        = l_Undef;
  insertOption(o_produce_stats, SMTOption(0));
//  produce_stats                 = 0;
//  produce_models                = 0;
  print_stats                   = 1;
  print_proofs_smtlib2          = 0;
  print_proofs_dotty	        = 0;
//  produce_inter                 = 0;
  dump_formula                  = 0;
//  verbosity                     = 2;
//  print_success                 = false;
  certification_level           = 0;
  strcpy( certifying_solver, "tool_wrapper.sh" );
  // Set SAT-Solver Default configuration
  sat_initial_skip_step         = 1;
  sat_skip_step_factor          = 1;
  sat_use_luby_restart          = 1;
  sat_learn_up_to_size          = 0;
  sat_temporary_learn           = 1;
  sat_preprocess_booleans       = 1;
  sat_preprocess_theory         = 0;
  sat_centrality                = 18;
  sat_trade_off                 = 8192;
  sat_minimize_conflicts        = 1;
  sat_dump_cnf                  = 0;
//  sat_dump_rnd_inter            = 0;
  sat_lazy_dtc                  = 0;
  sat_lazy_dtc_burst            = 1;
  // UF-Solver Default configuration
  uf_disable                    = 0;
  // BV-Solver Default configuration
  bv_disable                    = 0;
  // DL-Solver Default configuration
  dl_disable                    = 0;
  // LRA-Solver Default configuration
  lra_disable                   = 0;
  lra_poly_deduct_size          = 0;
  lra_integer_solver            = 0;
  lra_check_on_assert           = 0;
  // Proof parameters
//  proof_reduce                  = 0;
  proof_ratio_red_solv          = 0;
  proof_red_time                = 0;
//  proof_num_graph_traversals    = 0;
//  proof_red_trans               = 0;
  proof_reorder_pivots          = 0;
  proof_reduce_while_reordering = 0;
  proof_random_context_analysis = 0;
  proof_random_swap_application = 0;
  proof_remove_mixed            = 0;
//  proof_certify_inter           = 0;
  proof_random_seed	        = 0;
  sat_theory_polarity_suggestion = 1;
  cuf_bitwidth                   = 32;
}

void
SMTConfig::parseCMDLine( int argc
                       , char * argv[ ] )
{
  for ( int i = 1 ; i < argc - 1 ; i ++ )
  {
    const char * buf = argv[ i ];
    // Parsing of configuration options
//    if ( sscanf( buf, "--config=%s", config_name ) == 1 )
//    {
//      parseConfig( config_name );
//      break;
//    }
    if ( strcmp( buf, "--help" ) == 0
         || strcmp( buf, "-h" ) == 0 )
    {
      printHelp( );
      exit( 1 );
    }
    else
    {
      printHelp( );
      std::cerr << "unrecognized option" << buf << std::endl;
      exit(1);
    }
  }
}

void SMTConfig::printHelp( )
{
  const char help_string[]
    = "Usage: ./opensmt [OPTION] filename\n"
      "where OPTION can be\n"
      "  --help [-h]              print this help\n"
      "  --config=<filename>      use configuration file <filename>\n";
  std::cerr << help_string;
}
