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
const char* LIALogic::tk_int_minus = "-";
const char* LIALogic::tk_int_plus  = "+";
const char* LIALogic::tk_int_times = "*";
const char* LIALogic::tk_int_div   = "div";
const char* LIALogic::tk_int_mod   = "mod";
const char* LIALogic::tk_int_abs   = "abs";
const char* LIALogic::tk_int_lt    = "<";
const char* LIALogic::tk_int_leq   = "<=";
const char* LIALogic::tk_int_gt    = ">";
const char* LIALogic::tk_int_geq   = ">=";

const char* LIALogic::s_sort_integer = "Int";

LIALogic::LIALogic() :
    LALogic()
        , sym_Int_ZERO(SymRef_Undef)
        , sym_Int_ONE(SymRef_Undef)
        , sym_Int_NEG(SymRef_Undef)
        , sym_Int_MINUS(SymRef_Undef)
        , sym_Int_PLUS(SymRef_Undef)
        , sym_Int_TIMES(SymRef_Undef)
        , sym_Int_DIV(SymRef_Undef)
        , sym_Int_MOD(SymRef_Undef)
        , sym_Int_ABS(SymRef_Undef)
        , sym_Int_EQ(SymRef_Undef)
        , sym_Int_LEQ(SymRef_Undef)
        , sym_Int_LT(SymRef_Undef)
        , sym_Int_GEQ(SymRef_Undef)
        , sym_Int_GT(SymRef_Undef)
        , sym_Int_ITE(SymRef_Undef)
        , sort_INTEGER(SRef_Undef)
        , term_Int_ZERO(PTRef_Undef)
        , term_Int_ONE(PTRef_Undef)
        , term_Int_MINUSONE(PTRef_Undef)
        , split_eq(false)
{
    char* m;
    char** msg = &m;

    sort_INTEGER = declareSort(s_sort_integer, msg);
    ufsorts.remove(sort_INTEGER);

//    printf("Setting sort_REAL to %d at %p\n", sort_REAL.x, &(sort_REAL.x));
    vec<SRef> params;
    term_Int_ZERO = mkConst(sort_INTEGER, tk_int_zero);
    sym_Int_ZERO  = getSymRef(term_Int_ZERO);
    sym_store.setInterpreted(sym_Int_ZERO);

    term_Int_ONE  = mkConst(sort_INTEGER, tk_int_one);
    sym_Int_ONE   = getSymRef(term_Int_ONE);
    sym_store.setInterpreted(sym_Int_ONE);
    term_Int_MINUSONE  = mkConst(sort_INTEGER, "-1");
    params.push(sort_INTEGER);
    // Negation
    sym_Int_NEG = declareFun(tk_int_neg, sort_INTEGER, params, msg, true);
    sym_store.setInterpreted(sym_Int_NEG);
    sym_Int_ABS = declareFun(tk_int_abs, sort_INTEGER, params, msg, true);
    sym_store.setInterpreted(sym_Int_ABS);
    params.push(sort_INTEGER);
    sym_Int_MINUS = declareFun(tk_int_neg, sort_INTEGER, params, msg, true);
    sym_store[sym_Int_MINUS].setLeftAssoc();
    sym_store.setInterpreted(sym_Int_MINUS);
    sym_Int_PLUS  = declareFun(tk_int_plus, sort_INTEGER, params, msg, true);
    sym_store[sym_Int_PLUS].setNoScoping();
    sym_store[sym_Int_PLUS].setCommutes();
    sym_store[sym_Int_PLUS].setLeftAssoc();
    sym_store.setInterpreted(sym_Int_PLUS);
    sym_Int_TIMES = declareFun(tk_int_times, sort_INTEGER, params, msg, true);
    sym_store[sym_Int_TIMES].setNoScoping();
    sym_store[sym_Int_TIMES].setLeftAssoc();
    sym_store[sym_Int_TIMES].setCommutes();
    sym_store.setInterpreted(sym_Int_TIMES);
    sym_Int_DIV   = declareFun(tk_int_div, sort_INTEGER, params, msg, true);
    sym_store[sym_Int_DIV].setNoScoping();
    sym_store[sym_Int_DIV].setLeftAssoc();
    sym_store.setInterpreted(sym_Int_DIV);
    sym_Int_MOD   = declareFun(tk_int_mod, sort_INTEGER, params, msg, true);
    sym_store[sym_Int_MOD].setNoScoping();
    sym_store.setInterpreted(sym_Int_MOD);
    sym_Int_LEQ  = declareFun(tk_int_leq, sort_BOOL, params, msg, true);
    sym_store[sym_Int_LEQ].setNoScoping();
    sym_store[sym_Int_LEQ].setChainable();
    sym_store.setInterpreted(sym_Int_LEQ);
    sym_Int_LT   = declareFun(tk_int_lt, sort_BOOL, params, msg, true);
    sym_store[sym_Int_LT].setNoScoping();
    sym_store[sym_Int_LT].setChainable();
    sym_store.setInterpreted(sym_Int_LT);
    sym_Int_GEQ  = declareFun(tk_int_geq, sort_BOOL, params, msg, true);
    sym_store[sym_Int_GEQ].setNoScoping();
    sym_store[sym_Int_GEQ].setChainable();
    sym_store.setInterpreted(sym_Int_GEQ);
    sym_Int_GT   = declareFun(tk_int_gt, sort_BOOL, params, msg, true);
    sym_store[sym_Int_GT].setNoScoping();
    sym_store[sym_Int_GT].setChainable();
    sym_store.setInterpreted(sym_Int_GEQ);
    vec<SRef> ite_params;
    ite_params.push(sort_BOOL);
    ite_params.push(sort_INTEGER);
    ite_params.push(sort_INTEGER);
    sym_Int_ITE = declareFun(tk_ite, sort_INTEGER, ite_params, msg, true);
    //sym_store[sym_Real_ITE].setLeftAssoc();
    sym_store[sym_Int_ITE].setNoScoping();
    sym_store.setInterpreted(sym_Int_ITE);
}


PTRef LIALogic::sumToNormalizedInequality(PTRef sum) {
    vec<PTRef> varFactors;
    PTRef constant = PTRef_Undef;
    Pterm const & s = getPterm(sum);
    for (int i = 0; i < s.size(); i++) {
        if (isConstant(s[i])) {
            assert(constant == PTRef_Undef);
            constant = s[i];
        } else {
            assert(isLinearFactor(s[i]));
            varFactors.push(s[i]);
        }
    }
    if (constant == PTRef_Undef) { constant = getTerm_NumZero(); }
    auto constantValue = getNumConst(constant);
    termSort(varFactors);
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
    PTRef normalizedSum = varFactors.size() == 1 ? varFactors[0] : mkFun(get_sym_Num_PLUS(), varFactors);
    // 0 <= normalizedSum + constatValue
    // in LIA we can strengthen the inequality to
    // ceiling(-constantValue) <= normalizedSum
    constantValue.negate();
    constantValue = constantValue.ceil();
    return mkFun(get_sym_Num_LEQ(), {mkConst(constantValue), normalizedSum});
}

PTRef LIALogic::insertTerm(SymRef sym, vec<PTRef> &terms) {
    if (sym == get_sym_Int_MOD())
        return mkIntMod(terms);
    if (sym == get_sym_Int_DIV())
        return mkIntDiv(terms);
    return LALogic::insertTerm(sym, terms);
}

PTRef LIALogic::mkIntDiv(vec<PTRef> const & args) {
    if (args.size() != 2) { throw OsmtApiException("Incorrect number of arguments for DIV operator"); }
    return _mkIntDiv(args);
}

PTRef LIALogic::mkIntDiv(PTRef dividend, PTRef divisor) {
    return _mkIntDiv({dividend, divisor});
}

PTRef LIALogic::_mkIntDiv(const vec<PTRef> & args) {
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
    return insertTermHash(sym_Int_DIV, args);
}

PTRef LIALogic::mkIntMod(vec<PTRef> const & args) {
    if (args.size() != 2) { throw OsmtApiException("Incorrect number of arguments for MOD operator"); }
    return _mkIntMod(args);
}

PTRef LIALogic::mkIntMod(PTRef dividend, PTRef divisor) {
    return _mkIntMod({dividend, divisor});
}

PTRef LIALogic::_mkIntMod(vec<PTRef> const & args) {
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
    return insertTermHash(sym_Int_MOD, args);
}
