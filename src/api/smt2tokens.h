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
    t_writestate,
    t_readstate,
    t_simplify,
    t_writefuns,
    t_let,
    t_echo
};

extern std::unordered_map<token,std::string> tokenToName;

struct smt2token
{
    token x;
};
#endif
