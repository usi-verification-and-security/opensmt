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

#include "OsmtApiException.h"

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

LRALogic::LRALogic() :
    LALogic()
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
        , term_Real_MINUSONE(PTRef_Undef)
        , split_eq(false)
{
    char* m;
    char** msg = &m;
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
    term_Real_MINUSONE  = mkConst(sort_REAL, "-1");
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
    ites.insert(sym_Real_ITE, true);
    sortToIte.insert(sort_REAL, sym_Real_ITE);
    sym_store.setInterpreted(sym_Real_ITE);

    sym_Real_EQ = term_store.lookupSymbol(tk_equals, {term_Real_ZERO, term_Real_ZERO});
}

PTRef LRALogic::mkRealDiv(vec<PTRef> const & args)
{
    if (args.size() != 2) {
        throw OsmtApiException("Division operation requries exactly 2 arguments");
    }
    if (this->isNumZero(args[1])) {
        throw LADivisionByZeroException();
    }
    if (not isConstant(args[1])) {
        throw LANonLinearException("Only division by constant is permitted in linear arithmetic!");
    }
    SimplifyConstDiv simp(*this);
    vec<PTRef> args_new;
    SymRef s_new;
    simp.simplify(get_sym_Real_DIV(), args, s_new, args_new);
    if (isRealDiv(s_new)) {
        assert((isNumTerm(args_new[0]) || isNumPlus(args_new[0])) && isConstant(args_new[1]));
        args_new[1] = mkConst(FastRational_inverse(getNumConst(args_new[1]))); //mkConst(1/getRealConst(args_new[1]));
        return mkNumTimes(std::move(args_new));
    }
    PTRef tr = mkFun(s_new, std::move(args_new));
    return tr;
}

PTRef LRALogic::insertTerm(SymRef sym, vec<PTRef> &&terms) {
    if (sym == get_sym_Real_DIV())
        return mkRealDiv(terms);
    return LALogic::insertTerm(sym, std::move(terms));
}

/**
 * Normalizes a sum term a1x1 + a2xn + ... + anxn + c such that the leading coefficient is either 1 or -1.
 * Additionally, the normalized term is separated to constant and non-constant part, and the constant is modified as if
 * it was placed on the other side of an equality.
 *
 * @param sum
 * @return Constant part of the normalized sum as LHS and non-constant part of the normalized sum as RHS
 */

opensmt::pair<FastRational, PTRef> LRALogic::sumToNormalizedPair(PTRef sum) {

    auto [constantValue, varFactors] = getConstantAndFactors(sum);

    PTRef leadingFactor = varFactors[0];
    // normalize the sum according to the leading factor
    PTRef var, coeff;
    splitTermToVarAndConst(leadingFactor, var, coeff);
    opensmt::Number normalizationCoeff = abs(getNumConst(coeff));
    // varFactors come from a normalized sum, no need to call normalization code again
    PTRef normalizedSum = varFactors.size() == 1 ? varFactors[0] : mkFun(get_sym_Num_PLUS(), std::move(varFactors));
    if (normalizationCoeff != 1) {
        // normalize the whole sum
        normalizedSum = mkNumTimes(normalizedSum, mkConst(normalizationCoeff.inverse()));
        // DON'T forget to update also the constant factor!
        constantValue /= normalizationCoeff;
    }
    constantValue.negate(); // moving the constant to the LHS of the inequality
    return {std::move(constantValue), normalizedSum};
}

PTRef LRALogic::sumToNormalizedInequality(PTRef sum) {
    auto [lhsVal, rhs] = sumToNormalizedPair(sum);
    return mkFun(get_sym_Num_LEQ(), {mkConst(lhsVal), rhs});
}

PTRef LRALogic::sumToNormalizedEquality(PTRef sum) {
    auto [lhsVal, rhs] = sumToNormalizedPair(sum);
    return mkFun(get_sym_Num_EQ(), {mkConst(lhsVal), rhs});
}