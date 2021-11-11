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
const char* LRALogic::tk_real_minusone = "-1";
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
        , sort_REAL(declareSortAndCreateFunctions(s_sort_real))
        , term_Real_ZERO(mkConst(sort_REAL, tk_real_zero))
        , term_Real_ONE(mkConst(sort_REAL, tk_real_one))
        , term_Real_MINUSONE(mkConst(sort_REAL, tk_real_minusone))
        , sym_Real_ZERO(getSymRef(term_Real_ZERO))
        , sym_Real_ONE(getSymRef(term_Real_ONE))
        , sym_Real_NEG(declareFun_NoScoping(tk_real_neg, sort_REAL, {sort_REAL}))
        , sym_Real_MINUS(declareFun_NoScoping_LeftAssoc(tk_real_minus, sort_REAL, {sort_REAL, sort_REAL}))
        , sym_Real_PLUS(declareFun_Commutative_NoScoping_LeftAssoc(tk_real_plus, sort_REAL, {sort_REAL, sort_REAL}))
        , sym_Real_TIMES(declareFun_Commutative_NoScoping_LeftAssoc(tk_real_times, sort_REAL, {sort_REAL, sort_REAL}))
        , sym_Real_DIV(declareFun_NoScoping_LeftAssoc(tk_real_div, sort_REAL, {sort_REAL, sort_REAL}))
        , sym_Real_EQ(declareFun_Commutative_NoScoping_Chainable(tk_equals, sort_BOOL, {sort_REAL, sort_REAL}))
        , sym_Real_LEQ(declareFun_NoScoping_Chainable(tk_real_leq, sort_BOOL, {sort_REAL, sort_REAL}))
        , sym_Real_LT(declareFun_NoScoping_Chainable(tk_real_lt, sort_BOOL, {sort_REAL, sort_REAL}))
        , sym_Real_GEQ(declareFun_NoScoping_Chainable(tk_real_geq, sort_BOOL, {sort_REAL, sort_REAL}))
        , sym_Real_GT(declareFun_NoScoping_Chainable(tk_real_gt, sort_BOOL, {sort_REAL, sort_REAL}))
        , sym_Real_ITE(declareFun(tk_ite, sort_REAL, {sort_BOOL, sort_REAL, sort_REAL}))
        , split_eq(false)
{ }

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

opensmt::pair<opensmt::Number, PTRef> LRALogic::sumToNormalizedPair(PTRef sum) {

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