/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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

#ifndef OPENSMT_C_H
#define OPENSMT_C_H

#include "gmp.h"

#ifdef __cplusplus
extern "C" {
#endif

//
// Datatypes
//
typedef void * opensmt_expr;
typedef void * opensmt_context;
typedef enum { l_false=-1, l_undef, l_true } opensmt_result;
typedef enum
{
    qf_uf         // Uninterpreted Functions
  , qf_bv         // BitVectors
  , qf_rdl        // Real difference logics
  , qf_idl        // Integer difference logics
  , qf_lra        // Real linear arithmetic
  , qf_lia        // Integer linear arithmetic
  , qf_ufidl      // UF + IDL
  , qf_uflra      // UF + LRA
  , qf_bool       // Only booleans
  , qf_ct         // Cost 
} opensmt_logic;
//
// Communication APIs
//
void             opensmt_set_verbosity             ( opensmt_context, int );
char *           opensmt_version                   ( );
void             opensmt_print_expr                ( opensmt_expr );
opensmt_context  opensmt_mk_context                ( opensmt_logic );
void             opensmt_del_context               ( opensmt_context );
void             opensmt_reset                     ( opensmt_context );
void             opensmt_push                      ( opensmt_context );
void             opensmt_pop                       ( opensmt_context );
void             opensmt_assert                    ( opensmt_context, opensmt_expr );
opensmt_result   opensmt_check                     ( opensmt_context );
opensmt_result   opensmt_check_assump              ( opensmt_context, opensmt_expr );
opensmt_result   opensmt_check_lim_assump          ( opensmt_context, opensmt_expr, unsigned );
unsigned         opensmt_conflicts                 ( opensmt_context );
unsigned         opensmt_decisions                 ( opensmt_context );
opensmt_expr     opensmt_get_value                 ( opensmt_context, opensmt_expr );
void             opensmt_get_num                   ( opensmt_expr n, mpz_t val );
opensmt_result   opensmt_get_bool                  ( opensmt_context c, opensmt_expr p );
void             opensmt_prefer                    ( opensmt_expr a );
void             opensmt_polarity                  ( opensmt_context c, opensmt_expr a, int pos );


void             opensmt_print_model               ( opensmt_context, const char * );
void             opensmt_print_proof               ( opensmt_context, const char * );
void             opensmt_print_interpolant         ( opensmt_context, const char * );

void             opensmt_dump_assertions_to_file   ( opensmt_context, const char * );

//
// Formula construction APIs
//
opensmt_expr     opensmt_mk_true                   ( opensmt_context );
opensmt_expr     opensmt_mk_false                  ( opensmt_context );
opensmt_expr     opensmt_mk_bool_var               ( opensmt_context, char * );
opensmt_expr     opensmt_mk_int_var                ( opensmt_context, char * );
opensmt_expr     opensmt_mk_real_var               ( opensmt_context, char * );
/*
opensmt_expr     opensmt_mk_bv_var                 ( opensmt_context, char *, unsigned );
*/
opensmt_expr     opensmt_mk_cost_var               ( opensmt_context, char * );
opensmt_expr     opensmt_mk_or                     ( opensmt_context, opensmt_expr *, unsigned );
opensmt_expr     opensmt_mk_and                    ( opensmt_context, opensmt_expr *, unsigned );
opensmt_expr     opensmt_mk_eq                     ( opensmt_context, opensmt_expr, opensmt_expr );
/*
opensmt_expr     opensmt_mk_diseq                  ( opensmt_context, opensmt_expr, opensmt_expr );
*/
opensmt_expr     opensmt_mk_ite                    ( opensmt_context, opensmt_expr, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_not                    ( opensmt_context, opensmt_expr );
opensmt_expr     opensmt_mk_num_from_string        ( opensmt_context, const char * );
opensmt_expr     opensmt_mk_num_from_mpz           ( opensmt_context, const mpz_t );
opensmt_expr     opensmt_mk_num_from_mpq           ( opensmt_context, const mpq_t );
opensmt_expr     opensmt_mk_plus                   ( opensmt_context, opensmt_expr *, unsigned );
opensmt_expr     opensmt_mk_minus                  ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_times                  ( opensmt_context, opensmt_expr *, unsigned );
opensmt_expr     opensmt_mk_lt                     ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_leq                    ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_gt                     ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_geq                    ( opensmt_context, opensmt_expr, opensmt_expr );
/*
opensmt_expr     opensmt_mk_bv_constant            ( opensmt_context, unsigned, unsigned long );
opensmt_expr     opensmt_mk_bv_constant_from_string( opensmt_context, unsigned, const char * );
opensmt_expr     opensmt_mk_bv_add                 ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_sub                 ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_mul                 ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_minus               ( opensmt_context, opensmt_expr );
opensmt_expr     opensmt_mk_bv_concat              ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_and                 ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_or                  ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_xor                 ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_not                 ( opensmt_context, opensmt_expr );
opensmt_expr     opensmt_mk_bv_extract             ( opensmt_context, unsigned, unsigned, opensmt_expr );
opensmt_expr     opensmt_mk_bv_sign_extend         ( opensmt_context, opensmt_expr, unsigned );
opensmt_expr     opensmt_mk_bv_shift_left0         ( opensmt_context, opensmt_expr, unsigned );
opensmt_expr     opensmt_mk_bv_shift_left1         ( opensmt_context, opensmt_expr, unsigned );
opensmt_expr     opensmt_mk_bv_shift_right0        ( opensmt_context, opensmt_expr, unsigned );
opensmt_expr     opensmt_mk_bv_shift_right1        ( opensmt_context, opensmt_expr, unsigned );
opensmt_expr     opensmt_mk_bv_lt                  ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_le                  ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_gt                  ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_ge                  ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_slt                 ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_sle                 ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_sgt                 ( opensmt_context, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_bv_sge                 ( opensmt_context, opensmt_expr, opensmt_expr );
*/
opensmt_expr     opensmt_mk_ct_incur               ( opensmt_context, opensmt_expr, opensmt_expr, opensmt_expr );
opensmt_expr     opensmt_mk_ct_bound               ( opensmt_context, opensmt_expr, opensmt_expr );

#ifdef __cplusplus
}
#endif

#endif
