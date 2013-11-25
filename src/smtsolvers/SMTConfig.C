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

#include "SMTConfig.h"

/*********************************************************************
 * Generic configuration class, used for both set-info and set-option
 *********************************************************************/
// TODO destructor for ConfValue?

ConfValue::ConfValue(const char* s) {
    type = O_STR;
    strval = strdup(s); // TODO memory leak
}

ConfValue::ConfValue(const ASTNode& s_expr_n) {
    if (s_expr_n.getType() == SEXPRL_T) {
        type = O_LIST;
        configs = new list<ConfValue*>;
        for (list<ASTNode*>::iterator i = s_expr_n.children->begin(); i != s_expr_n.children->end(); i++)
            configs->push_back(new ConfValue(**i));
    }
    else if (s_expr_n.getType() == SYM_T) {
        type   = O_SYM;
        strval = strdup(s_expr_n.getValue());
    }
    else if (s_expr_n.getType() == SPECC_T) {
        ASTNode& spn = **(s_expr_n.children->begin());
        if (spn.getType() == NUM_T) {
           type = O_NUM;
           numval = atoi(spn.getValue());
        }
        else if (spn.getType() == DEC_T) {
            type = O_DEC;
            char* end;
            decval = strtod(spn.getValue(), &end);
            assert(end != NULL);
        }
        else if (spn.getType() == HEX_T) {
            type = O_HEX;
            string tmp(spn.getValue());
            tmp.erase(0,2);
            char* end;
            unumval = strtoul(tmp.c_str(), &end, 16);
            assert(end != NULL);
        }
        else if (spn.getType() == BIN_T) {
            type = O_BIN;
            string tmp(spn.getValue());
            tmp.erase(0,2);
            char* end;
            unumval = strtoul(tmp.c_str(), &end, 2);
            assert(end != NULL);
        }
        else if (spn.getType() == STR_T) {
            type = O_STR;
            strval = strdup(spn.getValue());
        }
        else assert(false);
    }
    else if (s_expr_n.getType() == UATTR_T) {
        type = O_ATTR;
        strval = strdup(s_expr_n.getValue());
    }
    else assert(false); //Not implemented
}

char* ConfValue::toString() const {
    if (type == O_BOOL)
        return numval == 1 ? strdup("true") : strdup("false");
    if (type == O_STR)
        return strdup(strval);
    if (type == O_NUM) {
        stringstream ss;
        ss << numval;
        return strdup(ss.str().c_str());
    }
    if (type == O_EMPTY) {
        return strdup("");
    }
    if (type == O_ATTR) {
        return strdup(strval);
    }
    if (type == O_DEC) {
        stringstream ss;
        ss << decval;
        return strdup(ss.str().c_str());
    }
    if (type == O_HEX) {
        stringstream ss;
        ss << unumval;
        return strdup(ss.str().c_str());
    }
    if (type == O_BIN) {
        stringstream ss;
        ss << unumval;
        return strdup(ss.str().c_str());
    }
    if (type == O_SYM) {
        return strdup(strval);
    }
    if (type == O_LIST) {
        stringstream ss;
        ss << "( ";
        for (list<ConfValue*>::iterator it = configs->begin(); it != configs->end(); it++) {
            ss << *((*it)->toString()); ss << " "; }
        ss << ")";
        return strdup(ss.str().c_str());
    }
    return strdup("not implemented");
}


/***********************************************************
 * Class defining the information, configured with set-info
 ***********************************************************/

Info::Info(ASTNode& n) {
    assert( n.getType() == UATTR_T || n.getType() == PATTR_T );
    if (n.children == NULL) {
        value.type = O_EMPTY;
        return;
    }
    else {
        // n is now attribute_value
        n = **(n.children->begin());

        if (n.getType() == SPECC_T) {
            value = ConfValue(n);
        }
        else if (n.getType() == SYM_T) {
            value.strval = strdup(n.getValue());
            value.type = O_STR;
            return;
        }
        else if (n.getType() == SEXPRL_T) {
            value = ConfValue(n);
        }
        else assert(false);
    }
}

/***********************************************************
 * Class defining the options, configured with set-config
 ***********************************************************/

Option::Option(ASTNode& n) {
    assert(n.children != NULL);

    n = **(n.children->begin());

    if (n.getType() == BOOL_T) {
        value.type   = O_BOOL;
        value.numval = strcmp(n.getValue(), "true") == 0 ? 1 : 0;
        return;
    }
    if (n.getType() == STR_T) {
        value.type   = O_STR;
        value.strval = strdup(n.getValue());
        return;
    }
    if (n.getType() == NUM_T) {
        value.type   = O_NUM;
        value.numval = atoi(n.getValue());
        return;
    }

    assert( n.getType() == UATTR_T || n.getType() == PATTR_T );
    // The option is an attribute

    if (n.children == NULL) {
        value.type = O_EMPTY;
        return;
    }
    else {
        // n is now attribute_value
        n = **(n.children->begin());

        if (n.getType() == SPECC_T) {
            value = ConfValue(n);
        }
        else if (n.getType() == SYM_T) {
            if (strcmp(n.getValue(), "true") == 0) {
                value.type = O_BOOL;
                value.numval = 1;
            }
            else if (strcmp(n.getValue(), "false") == 0) {
                value.type = O_BOOL;
                value.numval = 0;
            }
            else {
                value.strval = strdup(n.getValue());
                value.type = O_STR;
            }
            return;
        }
        else if (n.getType() == SEXPRL_T) {
            value = ConfValue(n);
            /*
            */
        }
        else assert(false);
    }
}

bool SMTConfig::setOption(const char* name, const Option& value) {
    // Special options:
    // stats_out
    if (strcmp(name, o_stats_out) == 0) {
        if (value.getValue().type != O_STR) return false;
        if (!optionTable.contains(name))
            stats_out.open(value.getValue().strval, std::ios_base::out);
        else if (strcmp(optionTable[name].getValue().strval, value.getValue().strval) != 0) {
            if (stats_out.is_open()) {
                stats_out.close();
                stats_out.open(value.getValue().strval, std::ios_base::out);
            }
        }
        else {}
    }

    // produce stats
    if (strcmp(name, o_produce_stats) == 0) {
        if (value.getValue().type != O_BOOL) return false;
        if (value.getValue().numval == 1) {
            // Gets set to true
            if (!optionTable.contains(o_stats_out)) {
                if (!optionTable.contains(o_produce_stats) || optionTable[o_produce_stats].getValue().numval == 0) {
                    // Insert the default value
                    optionTable.insert(o_stats_out, Option("/dev/stdout"));
                }
                else if (optionTable.contains(o_produce_stats) && optionTable[o_produce_stats].getValue().numval == 1)
                    assert(false);
            }
            else { } // No action required

            if (!stats_out.is_open()) stats_out.open(optionTable[o_stats_out].getValue().strval, std::ios_base::out);
        }
        else if (optionTable.contains(o_produce_stats) && optionTable[o_produce_stats].getValue().numval == 1) {
            // gets set to false and was previously true
            if (optionTable.contains(o_stats_out)) {
                if (optionTable[o_stats_out].getValue().numval == 0) assert(false);
                else if (stats_out.is_open()) stats_out.close();
            }
        }
    }

    if (strcmp(name, o_random_seed) == 0) {
        if (value.getValue().type != O_NUM) return false;
        int seed = value.getValue().numval;
        if (seed == 0) return false;
    }
    if (optionTable.contains(name))
        optionTable.remove(name);
    optionTable.insert(name, value);
    return true;
}

const Option& SMTConfig::getOption(const char* name) const {
    if (optionTable.contains(name))
        return optionTable[name];
    else
        return option_Empty;
}

bool SMTConfig::setInfo(const char* name, const Info& value) {
    if (infoTable.contains(name))
        infoTable.remove(name);
    infoTable.insert(name, value);
    return true;
}

const Info& SMTConfig::getInfo(const char* name) const {
    if (infoTable.contains(name))
        return infoTable[name];
    else
        return info_Empty;
}

const char* SMTConfig::o_incremental   = ":incremental";
const char* SMTConfig::o_produce_stats = ":produce-stats";
const char* SMTConfig::o_stats_out     = ":stats-out";
const char* SMTConfig::o_random_seed   = ":random-seed";

void
SMTConfig::initializeConfig( )
{
  // Set Global Default configuration
  logic                         = UNDEF;
  status                        = l_Undef;
//  incremental                   = 0;
  optionTable.insert(o_incremental, Option(0));
  optionTable.insert(o_produce_stats, Option(0));
//  produce_stats                 = 0;
  produce_models                = 0;
  print_stats                   = 0;
  print_proofs_smtlib2          = 0;
  print_proofs_dotty	        = 0;
  produce_inter                 = 0;
  dump_formula                  = 0;
//  verbosity                     = 2;
//  print_success                 = false;
  certification_level           = 0;       
  strcpy( certifying_solver, "tool_wrapper.sh" ); 
  // Set SAT-Solver Default configuration
  sat_theory_propagation        = 1;
  sat_polarity_mode             = 0;
  sat_initial_skip_step         = 1;
  sat_skip_step_factor          = 1;
  sat_restart_first             = 100;
  sat_restart_inc               = 1.1;
  sat_use_luby_restart          = 0;
  sat_learn_up_to_size          = INT_MAX;
  sat_temporary_learn           = 1;
  sat_preprocess_booleans       = 1;
  sat_preprocess_theory         = 0;
  sat_centrality                = 18;
  sat_trade_off                 = 8192;
  sat_minimize_conflicts        = 1;
  sat_dump_cnf                  = 0;
  sat_dump_rnd_inter            = 0;
  sat_lazy_dtc                  = 0;
  sat_lazy_dtc_burst            = 1;
  // UF-Solver Default configuration
  uf_disable                    = 0;
  uf_theory_propagation         = 1;
  // BV-Solver Default configuration
  bv_disable                    = 0;
  bv_theory_propagation         = 1;
  // DL-Solver Default configuration
  dl_disable                    = 0;
  dl_theory_propagation         = 1;
  // LRA-Solver Default configuration
  lra_disable                   = 0;
  lra_theory_propagation        = 1;
  lra_poly_deduct_size          = 0;
  lra_gaussian_elim             = 1;
  lra_integer_solver            = 0;
  lra_check_on_assert           = 0;
  // Proof parameters           
  proof_reduce                  = 0;
  proof_ratio_red_solv          = 0;
  proof_red_time                = 0;
  proof_num_graph_traversals    = 0;
  proof_red_trans               = 0;
  proof_reorder_pivots          = 0;
  proof_reduce_while_reordering = 0;
  proof_random_context_analysis = 0;
  proof_random_swap_application = 0;
  proof_remove_mixed            = 0;
  proof_set_inter_algo          = 1;
  proof_certify_inter           = 0;
  proof_random_seed	        = 0;
}

void SMTConfig::parseConfig ( char * f )
{
  FILE * filein = NULL;
  // Open configuration file
  if ( ( filein = fopen( f, "rt" ) ) == NULL )
  {
    // No configuration file is found. Print out
    // the current configuration
    // cerr << "# " << endl;
    cerr << "# WARNING: No configuration file " << f << ". Dumping default setting to " << f << endl;
    ofstream fileout( f );
    printConfig( fileout );
    fileout.close( );
  }
  else
  {
    int line = 0;

    while ( !feof( filein ) )
    {
      line ++;
      char buf[ 128 ];
      char * res = fgets( buf, 128, filein );
      (void)res;
      // Stop if finished
      if ( feof( filein ) )
	break;
      // Skip comments
      if ( buf[ 0 ] == '#' )
	continue;

      char tmpbuf[ 32 ];

      // GENERIC CONFIGURATION
//	   if ( sscanf( buf, "incremental %d\n"             , &incremental )                   == 1 );
//           if ( sscanf( buf, "produce_stats %d\n"           , &produce_stats )                 == 1 );
      if ( sscanf( buf, "print_stats %d\n"             , &print_stats )                   == 1 );
      else if ( sscanf( buf, "print_proofs_smtlib2 %d\n"    , &print_proofs_smtlib2 )          == 1 );
      else if ( sscanf( buf, "print_proofs_dotty %d\n"      , &print_proofs_dotty )            == 1 );
      else if ( sscanf( buf, "produce_models %d\n"          , &produce_models )                == 1 )
      {
#ifndef PRODUCE_PROOF
	if ( produce_proofs != 0 )
	  opensmt_error( "You must configure code with --enable-proof to produce proofs" );
#endif
      }
      else if ( sscanf( buf, "produce_inter %d\n"            , &produce_inter )                 == 1 )
      {
#ifndef PRODUCE_PROOF
	if ( produce_inter != 0 )
	  opensmt_error( "You must configure code with --enable-proof to produce interpolants" );
#endif
      }
      else if ( sscanf( buf, "regular_output_channel %s\n"   , tmpbuf )                         == 1 )
	setRegularOutputChannel( tmpbuf );
      else if ( sscanf( buf, "diagnostic_output_channel %s\n", tmpbuf )                         == 1 )
	setDiagnosticOutputChannel( tmpbuf );
      else if ( sscanf( buf, "dump_formula %d\n"             , &dump_formula )                  == 1 );
//      else if ( sscanf( buf, "verbosity %d\n"                , &verbosity )                     == 1 );
      else if ( sscanf( buf, "certification_level %d\n"      , &certification_level )           == 1 );
      else if ( sscanf( buf, "certifying_solver %s\n"        , certifying_solver )              == 1 );
      // SAT SOLVER CONFIGURATION                            
      else if ( sscanf( buf, "sat_theory_propagation %d\n"   , &(sat_theory_propagation))       == 1 );
      else if ( sscanf( buf, "sat_polarity_mode %d\n"        , &(sat_polarity_mode))            == 1 );
      else if ( sscanf( buf, "sat_initial_skip_step %lf\n"   , &(sat_initial_skip_step))        == 1 );
      else if ( sscanf( buf, "sat_skip_step_factor %lf\n"    , &(sat_skip_step_factor))         == 1 );
      else if ( sscanf( buf, "sat_restart_first %d\n"        , &(sat_restart_first))            == 1 );
      else if ( sscanf( buf, "sat_restart_increment %lf\n"   , &(sat_restart_inc))              == 1 );
      else if ( sscanf( buf, "sat_use_luby_restart %d\n"     , &(sat_use_luby_restart))         == 1 );
      else if ( sscanf( buf, "sat_learn_up_to_size %d\n"     , &(sat_learn_up_to_size))         == 1 );
      else if ( sscanf( buf, "sat_temporary_learn %d\n"      , &(sat_temporary_learn))          == 1 );
      else if ( sscanf( buf, "sat_preprocess_booleans %d\n"  , &(sat_preprocess_booleans))      == 1 );
      else if ( sscanf( buf, "sat_preprocess_theory %d\n"    , &(sat_preprocess_theory))        == 1 );
      else if ( sscanf( buf, "sat_centrality %d\n"           , &(sat_centrality))               == 1 );
      else if ( sscanf( buf, "sat_trade_off %d\n"            , &(sat_trade_off))                == 1 );
      else if ( sscanf( buf, "sat_minimize_conflicts %d\n"   , &(sat_minimize_conflicts))       == 1 );
      else if ( sscanf( buf, "sat_dump_cnf %d\n"             , &(sat_dump_cnf))                 == 1 );
      else if ( sscanf( buf, "sat_dump_rnd_inter %d\n"       , &(sat_dump_rnd_inter))           == 1 );
      else if ( sscanf( buf, "sat_lazy_dtc %d\n"             , &(sat_lazy_dtc))                 == 1 );
      else if ( sscanf( buf, "sat_lazy_dtc_burst %d\n"       , &(sat_lazy_dtc_burst))           == 1 );
      // PROOF PRODUCTION CONFIGURATION
      else if ( sscanf( buf, "proof_reduce %d\n"             , &(proof_reduce))                 == 1 );
      else if ( sscanf( buf, "proof_random_seed %d\n"        , &(proof_random_seed))            == 1 );
      else if ( sscanf( buf, "proof_ratio_red_solv %lf\n"    , &(proof_ratio_red_solv))         == 1 );
      else if ( sscanf( buf, "proof_red_time %lf\n"          , &(proof_red_time))               == 1 );
      else if ( sscanf( buf, "proof_num_graph_traversals %d\n" , &(proof_num_graph_traversals)) == 1 );
      else if ( sscanf( buf, "proof_red_trans %d\n"          , &(proof_red_trans))              == 1 );
      else if ( sscanf( buf, "proof_reorder_pivots %d\n"     , &(proof_reorder_pivots))         == 1 );
      else if ( sscanf( buf, "proof_reduce_while_reordering %d\n"     , &(proof_reduce_while_reordering))         == 1 );
      else if ( sscanf( buf, "proof_random_context_analysis %d\n"     , &(proof_random_context_analysis))         == 1 );
      else if ( sscanf( buf, "proof_random_swap_application %d\n"     , &(proof_random_swap_application))         == 1 );
      else if ( sscanf( buf, "proof_remove_mixed %d\n"       , &(proof_remove_mixed))           == 1 );
      else if ( sscanf( buf, "proof_set_inter_algo %d\n"     , &(proof_set_inter_algo))         == 1 );
      else if ( sscanf( buf, "proof_certify_inter %d\n"      , &(proof_certify_inter))          == 1 );
      // EUF SOLVER CONFIGURATION
      else if ( sscanf( buf, "uf_disable %d\n"               , &(uf_disable))                   == 1 );
      else if ( sscanf( buf, "uf_theory_propagation %d\n"    , &(uf_theory_propagation))        == 1 );
      // BV SOLVER CONFIGURATION                                                                      
      else if ( sscanf( buf, "bv_disable %d\n"               , &(bv_disable))                   == 1 );
      else if ( sscanf( buf, "bv_theory_propagation %d\n"    , &(bv_theory_propagation))        == 1 );
      // DL SOLVER CONFIGURATION                                                                      
      else if ( sscanf( buf, "dl_disable %d\n"               , &(dl_disable))                   == 1 );
      else if ( sscanf( buf, "dl_theory_propagation %d\n"    , &(dl_theory_propagation))        == 1 );
      // LRA SOLVER CONFIGURATION                                                                     
      else if ( sscanf( buf, "lra_disable %d\n"              , &(lra_disable))                  == 1 );
      else if ( sscanf( buf, "lra_theory_propagation %d\n"   , &(lra_theory_propagation))       == 1 );
      else if ( sscanf( buf, "lra_poly_deduct_size %d\n"     , &(lra_poly_deduct_size))         == 1 );
      else if ( sscanf( buf, "lra_gaussian_elim %d\n"        , &(lra_gaussian_elim))            == 1 );
      else if ( sscanf( buf, "lra_integer_solver %d\n"       , &(lra_integer_solver))           == 1 );
      else if ( sscanf( buf, "lra_check_on_assert %d\n"      , &(lra_check_on_assert))          == 1 );
      else
      {
	opensmt_error2( "unrecognized option ", buf );
      }
    }

    // Close
    fclose( filein );
  }

  if ( produceStats() ) stats_out.open( "stats.out" );
}

void SMTConfig::printConfig ( ostream & out )
{
  out << "#" << endl;
  out << "# OpenSMT Configuration File" << endl;
  out << "# . Options may be written in any order" << endl;
  out << "# . Unrecognized options will throw an error" << endl;
  out << "# . Use '#' for line comments" << endl;
  out << "# . Remove this file and execute opensmt to generate a new copy with default values" << endl;
  out << "#" << endl;
  out << "# GENERIC CONFIGURATION" << endl;
  out << "#" << endl;
  out << "# Enables incrementality (SMT-LIB 2.0 script-compatible)" << endl;
  out << "incremental "                << getOption(o_incremental).toString() << endl;
  out << "# Regular output channel " << endl;
  out << "regular_output_channel stdout" << endl;
  out << "# Diagnostic output channel " << endl;
  out << "diagnostic_output_channel stderr" << endl;
  out << "# Prints statistics in stats.out" << endl;
  out << "produce_stats "              << getOption(o_produce_stats).toString() << endl;
  out << "# Prints statistics to screen" << endl;
  out << "print_stats "              << print_stats << endl;
  out << "# Prints models" << endl;
  out << "produce_models "             << produce_models << endl;
  out << "# Prints proofs"  << endl;
  out << "print_proofs_smtlib2 "       << print_proofs_smtlib2 << endl;
  out << "print_proofs_dotty "         << print_proofs_dotty << endl;
  out << "# Prints interpolants" << endl;
  out << "produce_inter "              << produce_inter << endl;
  out << "# Dumps input formula (debugging)" << endl;
  out << "dump_formula "               << dump_formula << endl;
  out << "# Choose verbosity level" << endl;
//  out << "verbosity "                  << verbosity << endl;
  out << "# Choose certification level" << endl;
  out << "# 0 - don't certify" << endl;
  out << "# 1 - certify conflicts" << endl;
  out << "# 2 - certify conflicts, deductions " << endl;
  out << "# 3 - certify conflicts, deductions, theory calls " << endl;
  out << "certification_level " << certification_level << endl;
  out << "certifying_solver " << certifying_solver << endl;
  out << "#" << endl;
  out << "# SAT SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "# Enables theory propagation" << endl;
  out << "sat_theory_propagation "     << sat_theory_propagation << endl;
  out << "# Polarity mode for TAtoms and BAtoms" << endl;
  out << "# 0 - all true" << endl;
  out << "# 1 - all false" << endl;
  out << "# 2 - all random" << endl;
  out << "# 3 - heuristic TAtoms, true BAtoms" << endl;
  out << "# 4 - heuristic TAtoms, false BAtoms" << endl;
  out << "# 5 - heuristic TAtoms, random BAtoms" << endl;
  out << "sat_polarity_mode "  << sat_polarity_mode << endl;
  out << "# Initial and step factor for theory solver calls" << endl;
  out << "sat_initial_skip_step "   << sat_initial_skip_step << endl;
  out << "sat_skip_step_factor "    << sat_skip_step_factor << endl;
  out << "# Initial and increment conflict limits for restart" << endl;
  out << "sat_restart_first "       << sat_restart_first << endl;
  out << "sat_restart_increment "   << sat_restart_inc << endl;
  out << "sat_use_luby_restart "    << sat_use_luby_restart << endl;
  out << "# Learn theory-clauses up to the specified size (0 learns nothing)" << endl;
  out << "sat_learn_up_to_size "    << sat_learn_up_to_size << endl;
  out << "sat_temporary_learn "     << sat_temporary_learn << endl;
  out << "# Preprocess variables and clauses when possible" << endl;
  out << "sat_preprocess_booleans " << sat_preprocess_booleans << endl;
  out << "sat_preprocess_theory "   << sat_preprocess_theory << endl;
  out << "sat_centrality "          << sat_centrality << endl;
  out << "sat_trade_off "           << sat_trade_off << endl;
  out << "sat_minimize_conflicts "  << sat_minimize_conflicts << endl;
  out << "sat_dump_cnf "            << sat_dump_cnf << endl;
  out << "sat_dump_rnd_inter "      << sat_dump_rnd_inter << endl;
  out << "sat_lazy_dtc "            << sat_lazy_dtc << endl;
  out << "sat_lazy_dtc_burst "      << sat_lazy_dtc_burst << endl;
  out << "#" << endl;
  out << "# PROOF TRANSFORMER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "# Enable reduction" << endl;
  out << "proof_reduce "             << proof_reduce << endl;
  out << "# Randomly initialize seed for transformation" << endl;
  out << "proof_random_seed "     << proof_random_seed << endl;
  out << "# Reduction timeout w.r.t. solving time for each global iteration" << endl;
  out << "proof_ratio_red_solv "     << proof_ratio_red_solv << endl;
  out << "# Reduction timeout for each global iteration" << endl;
  out << "proof_red_time "           << proof_red_time << endl;
  out << "# Number of graph traversals for each global iteration" << endl;
  out << "proof_num_graph_traversals "   << proof_num_graph_traversals << endl;
  out << "# Number of reduction global iterations" << endl;
  out << "proof_red_trans "          << proof_red_trans << endl;
  out << "# Enable pivot reordering for interpolation" << endl;
  out << "proof_reorder_pivots "     << proof_reorder_pivots << endl;
  out << "proof_reduce_while_reordering "     << proof_reduce_while_reordering << endl;
  out << "# Randomize examination rule contexts" << endl;
  out << "proof_random_context_analysis " << proof_random_context_analysis << endl;
  out << "# Randomize application rules A1,A2,B2k" << endl;
  out << "proof_random_swap_application " << proof_random_swap_application << endl;
  out << "# Delete AB-mixed subtrees" << endl;
  out << "proof_remove_mixed "       << proof_remove_mixed << endl;
  out << "# Set to 0,1,2 to use McMillan, Pudlak or McMillan' interpolation algorithm" << endl;
  out << "proof_set_inter_algo "      << proof_set_inter_algo << endl;
  out << "# Choose certification level for interpolants" << endl;
  out << "# 0 - don't certify" << endl;
  out << "# 1 - certify final interpolant" << endl;
  out << "# 2 - certify final and theory interpolants" << endl;
  out << "proof_certify_inter "      << proof_certify_inter << endl;
  out << "#" << endl;
  out << "# EUF SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "uf_disable "               << uf_disable << endl;
  out << "uf_theory_propagation "    << uf_theory_propagation << endl;
  out << "#" << endl;
  out << "# BITVECTOR SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "bv_disable "               << bv_disable << endl;
  out << "bv_theory_propagation "    << bv_theory_propagation << endl;
  out << "#" << endl;
  out << "# DIFFERENCE LOGIC SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "dl_disable "               << dl_disable << endl;
  out << "dl_theory_propagation "    << dl_theory_propagation << endl;
  out << "#" << endl;
  out << "# LINEAR RATIONAL ARITHMETIC SOLVER CONFIGURATION" << endl;
  out << "#" << endl;
  out << "lra_disable "              << lra_disable << endl;
  out << "lra_theory_propagation "   << lra_theory_propagation << endl;
  out << "lra_poly_deduct_size "     << lra_poly_deduct_size << endl;
  out << "lra_gaussian_elim "        << lra_gaussian_elim << endl;
  out << "lra_check_on_assert "      << lra_check_on_assert << endl;
}

void
SMTConfig::parseCMDLine( int argc
                       , char * argv[ ] )
{
  char config_name[ 64 ];
  for ( int i = 1 ; i < argc - 1 ; i ++ )
  {
    const char * buf = argv[ i ];
    // Parsing of configuration options
    if ( sscanf( buf, "--config=%s", config_name ) == 1 )
    {
      parseConfig( config_name );
      break;
    }      
    else if ( strcmp( buf, "--help" ) == 0 
	   || strcmp( buf, "-h" ) == 0 )
    {
      printHelp( );
      exit( 1 );
    }
    else
    {
      printHelp( );
      opensmt_error2( "unrecognized option", buf );
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
  cerr << help_string;
}
