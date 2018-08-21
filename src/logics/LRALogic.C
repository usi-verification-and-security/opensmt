/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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
#include "SStore.h"
#include "PtStore.h"
#include "LRALogic.h"
#include "TreeOps.h"

const char* LRALogic::e_nonlinear_term = "Logic does not support nonlinear terms";

/***********************************************************
 * Class defining simplifications
 ***********************************************************/

//const char* LRALogic::tk_val_real_default = "1";
const char* LRALogic::tk_real_zero  = "0";
const char* LRALogic::tk_real_one   = "1";
const char* LRALogic::tk_real_neg   = "-";
const char* LRALogic::tk_real_minus = "-";
const char* LRALogic::tk_real_plus  = "+";
const char* LRALogic::tk_real_times = "*";
const char* LRALogic::tk_real_div   = "/";
const char* LRALogic::tk_real_lt    = "<";
const char* LRALogic::tk_real_leq   = "<=";
const char* LRALogic::tk_real_gt    = ">";
const char* LRALogic::tk_real_geq   = ">=";
const char* LRALogic::s_sort_real = "Real";

LRALogic::LRALogic(SMTConfig& c) :
        LALogic(c)
        , sym_Real_ZERO(SymRef_Undef)
        , sym_Real_ONE(SymRef_Undef)
        , sym_Real_NEG(SymRef_Undef)
        , sym_Real_MINUS(SymRef_Undef)
        , sym_Real_PLUS(SymRef_Undef)
        , sym_Real_TIMES(SymRef_Undef)
        , sym_Real_DIV(SymRef_Undef)
        , sym_Real_EQ(SymRef_Undef)
        , sym_Real_LEQ(SymRef_Undef)
        , sym_Real_LT(SymRef_Undef)
        , sym_Real_GEQ(SymRef_Undef)
        , sym_Real_GT(SymRef_Undef)
        , sym_Real_ITE(SymRef_Undef)
        , sort_REAL(SRef_Undef)
        , term_Real_ZERO(PTRef_Undef)
        , term_Real_ONE(PTRef_Undef)
        , split_eq(false)
{
    char* m;
    char** msg = &m;
    logic_type = QF_LRA;
    sort_REAL = declareSort(s_sort_real, msg);
    ufsorts.remove(sort_REAL);
//    printf("Setting sort_REAL to %d at %p\n", sort_REAL.x, &(sort_REAL.x));
    vec<SRef> params;
    term_Real_ZERO = mkConst(sort_REAL, tk_real_zero);
    sym_Real_ZERO  = getSymRef(term_Real_ZERO);
    sym_store.setInterpreted(sym_Real_ZERO);
    term_Real_ONE  = mkConst(sort_REAL, tk_real_one);
    sym_Real_ONE   = getSymRef(term_Real_ONE);
    sym_store.setInterpreted(sym_Real_ONE);
    params.push(sort_REAL);
    // Negation
    sym_Real_NEG = declareFun(tk_real_neg, sort_REAL, params, msg, true);
    sym_store.setInterpreted(sym_Real_NEG);
    params.push(sort_REAL);
    sym_Real_MINUS = declareFun(tk_real_neg, sort_REAL, params, msg, true);
    sym_store[sym_Real_MINUS].setLeftAssoc();
    sym_store.setInterpreted(sym_Real_MINUS);
    sym_Real_PLUS  = declareFun(tk_real_plus, sort_REAL, params, msg, true);
    sym_store[sym_Real_PLUS].setNoScoping();
    sym_store[sym_Real_PLUS].setCommutes();
    sym_store[sym_Real_PLUS].setLeftAssoc();
    sym_store.setInterpreted(sym_Real_PLUS);
    sym_Real_TIMES = declareFun(tk_real_times, sort_REAL, params, msg, true);
    sym_store[sym_Real_TIMES].setNoScoping();
    sym_store[sym_Real_TIMES].setLeftAssoc();
    sym_store[sym_Real_TIMES].setCommutes();
    sym_store.setInterpreted(sym_Real_TIMES);
    sym_Real_DIV   = declareFun(tk_real_div, sort_REAL, params, msg, true);
    sym_store[sym_Real_DIV].setNoScoping();
    sym_store[sym_Real_DIV].setLeftAssoc();
    sym_store.setInterpreted(sym_Real_DIV);
    sym_Real_LEQ  = declareFun(tk_real_leq, sort_BOOL, params, msg, true);
    sym_store[sym_Real_LEQ].setNoScoping();
    sym_store[sym_Real_LEQ].setChainable();
    sym_store.setInterpreted(sym_Real_LEQ);
    sym_Real_LT   = declareFun(tk_real_lt, sort_BOOL, params, msg, true);
    sym_store[sym_Real_LT].setNoScoping();
    sym_store[sym_Real_LT].setChainable();
    sym_store.setInterpreted(sym_Real_LT);
    sym_Real_GEQ  = declareFun(tk_real_geq, sort_BOOL, params, msg, true);
    sym_store[sym_Real_GEQ].setNoScoping();
    sym_store[sym_Real_GEQ].setChainable();
    sym_store.setInterpreted(sym_Real_GEQ);
    sym_Real_GT   = declareFun(tk_real_gt, sort_BOOL, params, msg, true);
    sym_store[sym_Real_GT].setNoScoping();
    sym_store[sym_Real_GT].setChainable();
    sym_store.setInterpreted(sym_Real_GEQ);
    vec<SRef> ite_params;
    ite_params.push(sort_BOOL);
    ite_params.push(sort_REAL);
    ite_params.push(sort_REAL);
    sym_Real_ITE = declareFun(tk_ite, sort_REAL, ite_params, msg, true);
    //sym_store[sym_Real_ITE].setLeftAssoc();
    sym_store[sym_Real_ITE].setNoScoping();
    sym_store.setInterpreted(sym_Real_ITE);
}

const SymRef LRALogic::get_sym_Num_TIMES () const {return sym_Real_TIMES;}
const SymRef LRALogic::get_sym_Num_DIV () const {return sym_Real_DIV;}
const SymRef LRALogic::get_sym_Num_MINUS () const {return sym_Real_MINUS;}
const SymRef LRALogic::get_sym_Num_PLUS () const {return sym_Real_PLUS;}
const SymRef LRALogic::get_sym_Num_NEG () const {return sym_Real_NEG;}
const SymRef LRALogic::get_sym_Num_LEQ () const {return sym_Real_LEQ;}
const SymRef LRALogic::get_sym_Num_GEQ () const {return sym_Real_GEQ;}
const SymRef LRALogic::get_sym_Num_LT () const {return sym_Real_LT;}
const SymRef LRALogic::get_sym_Num_GT () const {return sym_Real_GT;}
const SymRef LRALogic::get_sym_Num_EQ () const {return sym_Real_EQ;}
const SymRef LRALogic::get_sym_Num_ZERO () const {return sym_Real_ZERO;}
const SymRef LRALogic::get_sym_Num_ONE () const {return sym_Real_ONE;}
const SymRef LRALogic::get_sym_Num_ITE () const {return sym_Real_ITE;}
const SRef LRALogic::get_sort_NUM () const {return sort_REAL;}

PTRef    LRALogic::getTerm_NumZero() const  { return term_Real_ZERO; }
PTRef      LRALogic::getTerm_NumOne()  const  { return term_Real_ONE; }
bool        LRALogic::hasSortNum(PTRef tr) const  { return hasSortReal(getPterm(tr).symb()); }
