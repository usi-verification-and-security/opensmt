#include "SStore.h"
#include "PtStore.h"
#include "LIALogic.h"
#include "TreeOps.h"

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
const char* LIALogic::tk_int_div   = "/";
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

bool LIALogic::isBuiltinSort(SRef sr) const  { return sr == sort_INTEGER || Logic::isBuiltinSort(sr); }
bool  LIALogic::isNonnegNumConst(PTRef tr) const  { return isNumConst(tr) && getNumConst(tr) >= 0; }

//SRef   declareSort_Integer(char** msg);
SRef   LIALogic::getSort_num()  const  {return sort_INTEGER;}


bool        LIALogic::isIntPlus(SymRef sr)  const { return sr == sym_Int_PLUS; }
bool        LIALogic::isNumPlus(PTRef tr)   const  { return isIntPlus(getPterm(tr).symb()); }
bool        LIALogic::isIntMinus(SymRef sr) const { return sr == sym_Int_MINUS; }
bool        LIALogic::isNumMinus(PTRef tr)  const  { return isIntMinus(getPterm(tr).symb()); }
bool        LIALogic::isIntNeg(SymRef sr)   const { return sr == sym_Int_NEG; }
bool        LIALogic::isNumNeg(PTRef tr)    const  { return isIntNeg(getPterm(tr).symb()); }
bool        LIALogic::isIntTimes(SymRef sr) const { return sr == sym_Int_TIMES; }
bool        LIALogic::isNumTimes(PTRef tr)  const  { return isIntTimes(getPterm(tr).symb()); }
bool        LIALogic::isIntDiv(SymRef sr)   const { return sr == sym_Int_DIV; }
bool        LIALogic::isNumDiv(PTRef tr)    const  { return isIntDiv(getPterm(tr).symb()); }
bool        LIALogic::isIntEq(SymRef sr)    const { return isEquality(sr) && (sym_store[sr][0] == sort_INTEGER); }
bool        LIALogic::isNumEq(PTRef tr)     const  { return isIntEq(getPterm(tr).symb()); }
bool        LIALogic::isIntLeq(SymRef sr)   const { return sr == sym_Int_LEQ; }
bool        LIALogic::isNumLeq(PTRef tr)    const  { return isIntLeq(getPterm(tr).symb()); }
bool        LIALogic::isIntLt(SymRef sr)    const { return sr == sym_Int_LT; }
bool        LIALogic::isNumLt(PTRef tr)     const  { return isIntLt(getPterm(tr).symb()); }
bool        LIALogic::isIntGeq(SymRef sr)   const { return sr == sym_Int_GEQ; }
bool        LIALogic::isNumGeq(PTRef tr)    const  { return isIntGeq(getPterm(tr).symb()); }
bool        LIALogic::isIntGt(SymRef sr)    const { return sr == sym_Int_GT; }
bool        LIALogic::isNumGt(PTRef tr)     const  { return isIntGt(getPterm(tr).symb()); }
bool        LIALogic::isIntVar(SymRef sr)   const { return isVar(sr) && sym_store[sr].rsort() == sort_INTEGER; }
bool        LIALogic::isIntVarOrIte(SymRef sr) const { return isIntVar(sr) || (isIte(sr) && sym_store[sr].rsort() == sort_INTEGER); }
bool        LIALogic::isNumVar(PTRef tr)    const  { return isIntVar(getPterm(tr).symb());}
bool        LIALogic::isIntZero(SymRef sr)  const { return sr == sym_Int_ZERO; }
bool        LIALogic::isNumZero(PTRef tr)   const  { return tr == term_Int_ZERO; }
bool        LIALogic::isIntOne(SymRef sr)   const { return sr == sym_Int_ONE; }
bool        LIALogic::isNumOne(PTRef tr)    const  { return tr == term_Int_ONE; }
bool        LIALogic::hasSortInt(SymRef sr) const { return sym_store[sr].rsort() == sort_INTEGER; }
bool        LIALogic::hasSortNum(PTRef tr) const  { return hasSortInt(getPterm(tr).symb()); }
PTRef       LIALogic::getTerm_NumZero() const  { return term_Int_ZERO; }
PTRef      LIALogic::getTerm_NumOne()  const  { return term_Int_ONE; }
PTRef      LIALogic::getTerm_NumMinusOne()  const  { return term_Int_MINUSONE; }


const SymRef LIALogic::get_sym_Num_TIMES () const {return sym_Int_TIMES;}
const  SymRef LIALogic::get_sym_Num_DIV () const {return sym_Int_DIV;}
const  SymRef LIALogic::get_sym_Num_MINUS () const {return sym_Int_MINUS;}
const SymRef LIALogic::get_sym_Num_PLUS () const {return sym_Int_PLUS;}
const SymRef LIALogic::get_sym_Num_NEG () const {return sym_Int_NEG;}
const SymRef LIALogic::get_sym_Num_LEQ () const {return sym_Int_LEQ;}
const SymRef LIALogic::get_sym_Num_GEQ () const {return sym_Int_GEQ;}
const SymRef LIALogic::get_sym_Num_LT () const {return sym_Int_LT;}
const SymRef LIALogic::get_sym_Num_GT () const {return sym_Int_GT;}
const SymRef LIALogic::get_sym_Num_EQ () const {return sym_Int_EQ;}
const SymRef LIALogic::get_sym_Num_ZERO () const {return sym_Int_ZERO;}
const SymRef LIALogic::get_sym_Num_ONE () const {return sym_Int_ONE;}
const SymRef LIALogic::get_sym_Num_ITE () const {return sym_Int_ITE;}
const SRef LIALogic::get_sort_NUM () const {return sort_INTEGER;}

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
        assert(isNumVarOrIte(var) and isNumConst(coeff));
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
