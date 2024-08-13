/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2016 Antti Hyvarinen

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


#ifndef APITOKENS_H
#define APITOKENS_H

#include <string>
#include <unordered_map>
#include <unordered_set>

namespace opensmt::tokens {
//
// The names for the tokens in the API for smtlib
//
    enum token {
        t_none,
        t_as,
        t_DECIMAL,
        t_NUMERAL,
        t_par,
        t_STRING,
        t_exists,
        t_forall,
        t_assert,
        t_checksat,
        t_declaresort,
        t_definesort,
        t_declarefun,
        t_declareconst,
        t_definefun,
        t_exit,
        t_getassertions,
        t_getassignment,
        t_getinfo,
        t_setinfo,
        t_getoption,
        t_setoption,
        t_getproof,
        t_getunsatcore,
        t_getvalue,
        t_getmodel,
        t_pop,
        t_push,
        t_setlogic,
        t_getinterpolants,
        t_theory,
        t_simplify,
        t_let,
        t_echo
    };
    inline const std::unordered_set<std::string> tokenNames = {
        "none",
        "as",
        "decimal",
        "numeral",
        "par",
        "string",
        "exists",
        "forall",
        "assert",
        "check-sat",
        "declare-sort",
        "define-sort",
        "declare-fun",
        "declare-const",
        "define-fun",
        "exit",
        "get-assertions",
        "get-assignment",
        "get-info",
        "set-info",
        "get-option",
        "set-option",
        "get-proof",
        "get-unsat-core",
        "get-value",
        "get-model",
        "pop",
        "push",
        "set-logic",
        "get-interpolants",
        "theory",
        "write-state",
        "read-state",
        "simplify",
        "write-funs",
        "let",
        "echo"
    };
    inline const std::unordered_map<token, std::string> tokenToName = {
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
        {t_simplify, "simplify"},
        {t_let, "let"},
        {t_echo, "echo"}
    };

    struct smt2token {
        token x;
    };

}

#endif
