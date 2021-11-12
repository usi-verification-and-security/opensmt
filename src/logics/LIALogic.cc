#include "SStore.h"
#include "PtStore.h"
#include "LIALogic.h"
#include "TreeOps.h"
#include "OsmtApiException.h"

const char* LIALogic::e_nonlinear_term = "Logic does not support nonlinear terms";

/***********************************************************
 * Class defining simplifications
 ***********************************************************/

const char* LIALogic::tk_int_zero  = "0";
const char* LIALogic::tk_int_one   = "1";
const char* LIALogic::tk_int_neg   = "-";
const char* LIALogic::tk_int_minusone = "-1";
const char* LIALogic::tk_int_minus = "-";
const char* LIALogic::tk_int_plus  = "+";
const char* LIALogic::tk_int_times = "*";
const char* LIALogic::tk_int_div   = "div";
const char* LIALogic::tk_int_mod   = "mod";
const char* LIALogic::tk_int_lt    = "<";
const char* LIALogic::tk_int_leq   = "<=";
const char* LIALogic::tk_int_gt    = ">";
const char* LIALogic::tk_int_geq   = ">=";

const char* LIALogic::s_sort_integer = "Int";

LIALogic::LIALogic() :
          LALogic()
        , sort_INTEGER(declareSortAndCreateFunctions(s_sort_integer))
        , term_Int_ZERO(mkConst(sort_INTEGER, tk_int_zero))
        , term_Int_ONE(mkConst(sort_INTEGER, tk_int_one))
        , term_Int_MINUSONE(mkConst(sort_INTEGER, tk_int_minusone))
        , sym_Int_ZERO(getSymRef(term_Int_ZERO))
        , sym_Int_ONE(getSymRef(term_Int_ONE))
        , sym_Int_NEG(declareFun_NoScoping(tk_int_neg, sort_INTEGER, {sort_INTEGER}))
        , sym_Int_MINUS(declareFun_NoScoping_LeftAssoc(tk_int_minus, sort_INTEGER, {sort_INTEGER, sort_INTEGER}))
        , sym_Int_PLUS(declareFun_Commutative_NoScoping_LeftAssoc(tk_int_plus, sort_INTEGER, {sort_INTEGER, sort_INTEGER}))
        , sym_Int_TIMES(declareFun_Commutative_NoScoping_LeftAssoc(tk_int_times, sort_INTEGER, {sort_INTEGER, sort_INTEGER}))
        , sym_Int_DIV(declareFun_NoScoping_LeftAssoc(tk_int_div, sort_INTEGER, {sort_INTEGER, sort_INTEGER}))
        , sym_Int_MOD(declareFun_NoScoping(tk_int_mod, sort_INTEGER, {sort_INTEGER, sort_INTEGER}))
        , sym_Int_EQ(sortToEquality[sort_INTEGER])
        , sym_Int_LEQ(declareFun_NoScoping_Chainable(tk_int_leq, sort_BOOL, {sort_INTEGER, sort_INTEGER}))
        , sym_Int_LT(declareFun_NoScoping_Chainable(tk_int_lt, sort_BOOL, {sort_INTEGER, sort_INTEGER}))
        , sym_Int_GEQ(declareFun_NoScoping_Chainable(tk_int_geq, sort_BOOL, {sort_INTEGER, sort_INTEGER}))
        , sym_Int_GT(declareFun_NoScoping_Chainable(tk_int_gt, sort_BOOL, {sort_INTEGER, sort_INTEGER}))
        , sym_Int_ITE(sortToIte[sort_INTEGER])
        , sym_Int_DISTINCT(sortToDisequality[sort_INTEGER])
        , split_eq(false)
{ }

/**
 * Normalizes a sum term a1x1 + a2xn + ... + anxn + c such that the coefficients of non-constant terms are coprime integers
 * Additionally, the normalized term is separated to constant and non-constant part, and the constant is modified as if
 * it was placed on the other side of an equality.
 * Note that the constant part can be a non-integer number after normalization.
 *
 * @param sum
 * @return Constant part of the normalized sum as LHS and non-constant part of the normalized sum as RHS
 */
opensmt::pair<FastRational, PTRef> LIALogic::sumToNormalizedPair(PTRef sum) {

    auto [constantValue, varFactors] = getConstantAndFactors(sum);

    vec<PTRef> vars; vars.capacity(varFactors.size());
    std::vector<opensmt::Number> coeffs; coeffs.reserve(varFactors.size());
    for (PTRef factor : varFactors) {
        PTRef var;
        PTRef coeff;
        splitTermToVarAndConst(factor, var, coeff);
        assert(LALogic::isNumVarLike(var) and isNumConst(coeff));
        vars.push(var);
        coeffs.push_back(getNumConst(coeff));
    }
    bool changed = false; // Keep track if any change to varFactors occurs

    bool allIntegers = std::all_of(coeffs.begin(), coeffs.end(),
        [](opensmt::Number const & coeff) { return coeff.isInteger(); });
    if (not allIntegers) {
        // first ensure that all coeffs are integers
        using Integer = FastRational; // TODO: change when we have FastInteger
        auto lcmOfDenominators = Integer(1);
        auto accumulateLCMofDenominators = [&lcmOfDenominators](FastRational const & next) {
            if (next.isInteger()) {
                // denominator is 1 => lcm of denominators stays the same
                return;
            }
            Integer den = next.get_den();
            if (lcmOfDenominators == 1) {
                lcmOfDenominators = std::move(den);
                return;
            }
            lcmOfDenominators = lcm(lcmOfDenominators, den);
        };
        std::for_each(coeffs.begin(), coeffs.end(), accumulateLCMofDenominators);
        for (auto & coeff : coeffs) {
            coeff *= lcmOfDenominators;
            assert(coeff.isInteger());
        }
        // DONT forget to update also the constant factor
        constantValue *= lcmOfDenominators;
        changed = true;
    }
    assert(std::all_of(coeffs.begin(), coeffs.end(), [](opensmt::Number const & coeff) { return coeff.isInteger(); }));
    // Now make sure all coeffs are coprime
    auto coeffs_gcd = abs(coeffs[0]);
    for (std::size_t i = 1; i < coeffs.size() && coeffs_gcd != 1; ++i) {
        coeffs_gcd = gcd(coeffs_gcd, abs(coeffs[i]));
        assert(coeffs_gcd.isInteger());
    }
    if (coeffs_gcd != 1) {
        for (auto & coeff : coeffs) {
            coeff /= coeffs_gcd;
            assert(coeff.isInteger());
        }
        // DONT forget to update also the constant factor
        constantValue /= coeffs_gcd;
        changed = true;
    }
    // update the factors
    if (changed) {
        for (int i = 0; i < varFactors.size(); ++i) {
            varFactors[i] = mkNumTimes(vars[i], mkConst(coeffs[i]));
        }
    }
    PTRef normalizedSum = varFactors.size() == 1 ? varFactors[0] : mkFun(get_sym_Num_PLUS(), std::move(varFactors));
    // 0 <= normalizedSum + constatValue
    constantValue.negate();
    return {std::move(constantValue), normalizedSum};
}


PTRef LIALogic::sumToNormalizedInequality(PTRef sum) {
    auto [lhsVal, rhs] = sumToNormalizedPair(sum);
    return mkFun(get_sym_Num_LEQ(), {mkConst(lhsVal.ceil()), rhs});
}

PTRef LIALogic::sumToNormalizedEquality(PTRef sum) {
    auto [lhsVal, rhs] = sumToNormalizedPair(sum);
    if (not lhsVal.isInteger()) { return getTerm_false(); }
    return mkFun(get_sym_Num_EQ(), {mkConst(lhsVal), rhs});
}

PTRef LIALogic::insertTerm(SymRef sym, vec<PTRef> && terms) {
    if (extendedSignatureEnabled()) {
        if (sym == get_sym_Int_MOD())
            return mkIntMod(std::move(terms));
        if (sym == get_sym_Int_DIV())
            return mkIntDiv(std::move(terms));
    }
    return LALogic::insertTerm(sym, std::move(terms));
}

PTRef LIALogic::mkIntDiv(vec<PTRef> && args) {
    if (args.size() != 2) { throw OsmtApiException("Incorrect number of arguments for DIV operator"); }
    return _mkIntDiv(std::move(args));
}

PTRef LIALogic::mkIntDiv(PTRef dividend, PTRef divisor) {
    return _mkIntDiv({dividend, divisor});
}

PTRef LIALogic::_mkIntDiv(vec<PTRef> && args) {
    assert(args.size() == 2);
    PTRef dividend = args[0];
    PTRef divisor = args[1];
    if (not isConstant(divisor)) { throw LANonLinearException("Divisor must be constant in linear logic"); }
    if (isNumZero(divisor)) { throw LADivisionByZeroException(); }

    if (isConstant(dividend)) {
        auto const& dividendValue = getNumConst(dividend);
        auto const& divisorValue = getNumConst(divisor);
        assert(dividendValue.isInteger() and divisorValue.isInteger());
        // evaluate immediately the operation on two constants
        auto realDiv = dividendValue / divisorValue;
        auto intDiv = divisorValue.sign() > 0 ? realDiv.floor() : realDiv.ceil();
        return mkConst(intDiv);
    }
    return mkFun(sym_Int_DIV, std::move(args));
}

PTRef LIALogic::mkIntMod(vec<PTRef> && args) {
    if (args.size() != 2) { throw OsmtApiException("Incorrect number of arguments for MOD operator"); }
    return _mkIntMod(std::move(args));
}

PTRef LIALogic::mkIntMod(PTRef dividend, PTRef divisor) {
    return _mkIntMod({dividend, divisor});
}

PTRef LIALogic::_mkIntMod(vec<PTRef> && args) {
    assert(args.size() == 2);
    PTRef dividend = args[0];
    PTRef divisor = args[1];
    if (not isNumConst(divisor)) { throw OsmtApiException("Divisor must be constant in linear logic"); }
    if (isNumZero(divisor)) { throw LADivisionByZeroException(); }

    if (isConstant(dividend)) {
        auto const& dividendValue = getNumConst(dividend);
        auto const& divisorValue = getNumConst(divisor);
        assert(dividendValue.isInteger() and divisorValue.isInteger());
        // evaluate immediately the operation on two constants
        auto realDiv = dividendValue / divisorValue;
        auto intDiv = divisorValue.sign() > 0 ? realDiv.floor() : realDiv.ceil();
        auto intMod = dividendValue - intDiv * divisorValue;
        assert(intMod.sign() >= 0 and intMod < abs(divisorValue));
        return mkConst(intMod);
    }
    return mkFun(sym_Int_MOD, std::move(args));
}
