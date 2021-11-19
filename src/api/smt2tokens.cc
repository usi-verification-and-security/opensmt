//
// Created by Antti on 19.11.21.
//
#include "smt2tokens.h"

std::unordered_map<token,std::string> tokenToName = {
    {t_none, "none"},
    {t_as, "as"},
    {t_DECIMAL, "decimal"},
    {t_NUMERAL, "numeral"},
    {t_par, "par"},
    {t_STRING, "string"},
    {t_exists, "exists"},
    {t_forall, "forall"},
    {t_assert, "assert"},
    {t_checksat, "check-sat"},
    {t_declaresort, "declare-sort"},
    {t_definesort, "define-sort"},
    {t_declarefun, "declare-fun"},
    {t_declareconst, "declare-const"},
    {t_definefun, "define-fun"},
    {t_exit, "exit"},
    {t_getassertions, "get-assertions"},
    {t_getassignment, "get-assignment"},
    {t_getinfo, "get-info"},
    {t_setinfo, "set-info"},
    {t_getoption, "get-option"},
    {t_setoption, "set-option"},
    {t_getproof, "get-proof"},
    {t_getunsatcore, "get-unsat-core"},
    {t_getvalue, "get-value"},
    {t_getmodel, "get-model"},
    {t_pop, "pop"},
    {t_push, "push"},
    {t_setlogic, "set-logic"},
    {t_getinterpolants, "get-interpolants"},
    {t_theory, "theory"},
    {t_writestate, "write-state"},
    {t_readstate, "read-state"},
    {t_simplify, "simplify"},
    {t_writefuns, "write-funs"},
    {t_let, "let"},
    {t_echo, "echo"}
};