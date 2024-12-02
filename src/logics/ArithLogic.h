#ifndef LALOGIC_H
#define LALOGIC_H

#include "Logic.h"

#include <common/numbers/Number.h>

#include <numeric>

namespace opensmt {

class ArithDivisionByZeroException : public std::runtime_error {
public:
    ArithDivisionByZeroException() : runtime_error("Explicit division by zero encountered!") {}
    ~ArithDivisionByZeroException() = default;
};

class ArithLogic : public Logic {
public:
    ArithLogic(Logic_t type);
    ~ArithLogic() {
        for (auto number : numbers) {
            delete number;
        }
    }
    ArithLogic(ArithLogic const &) = delete;
    ArithLogic & operator=(ArithLogic const &) = delete;
    ArithLogic(ArithLogic &&) = default;
    ArithLogic & operator=(ArithLogic &&) = delete;

    bool isBuiltinFunction(SymRef sr) const override;
    PTRef insertTerm(SymRef sym, vec<PTRef> && terms) override;
    SRef getSort_real() const { return sort_REAL; }
    SRef getSort_int() const { return sort_INT; }
    PTRef mkConst(char const * name) override;
    PTRef mkConst(SRef s, char const * name) override;
    PTRef mkConst(SRef s, std::string const & name) { return mkConst(s, name.c_str()); }
    PTRef mkConst(SRef s, Number const & c);
    PTRef mkIntConst(Number const & c) {
        if (not hasIntegers()) { throw ApiException("Create Int constant in non-integral logic"); }
        return mkConst(getSort_int(), c);
    }
    PTRef mkRealConst(Number const & c) {
        if (not hasReals()) { throw ApiException("Create Real constant in non-real logic"); }
        return mkConst(getSort_real(), c);
    }
    PTRef mkIntVar(char const * name) {
        if (not hasIntegers()) { throw ApiException("Create Int var in non-integral logic"); }
        return mkVar(sort_INT, name, false);
    }
    PTRef mkRealVar(char const * name) {
        if (not hasReals()) { throw ApiException("Create Real var in non-real logic"); }
        return mkVar(sort_REAL, name, false);
    }

    bool isBuiltinSort(SRef sr) const override {
        return sr == getSort_int() || sr == getSort_real() || Logic::isBuiltinSort(sr);
    }
    bool isBuiltinSortSym(SSymRef ssr) const override {
        return ssr == sort_store.getSortSym(getSort_int()) || ssr == sort_store.getSortSym(getSort_real()) ||
               Logic::isBuiltinSortSym(ssr);
    }
    bool isBuiltinConstant(SymRef sr) const override {
        return (isIntConst(sr) || isRealConst(sr) || Logic::isBuiltinConstant(sr));
    }

    bool isNumConst(SymRef sr) const { return Logic::isConstant(sr) && yieldsSortNum(sr); }
    bool isNumConst(PTRef tr) const { return isNumConst(getPterm(tr).symb()); }
    bool isIntConst(SymRef sr) const { return isNumConst(sr) && yieldsSortInt(sr); }
    bool isIntConst(PTRef tr) const { return isIntConst(getPterm(tr).symb()); }
    bool isRealConst(SymRef sr) const { return isNumConst(sr) && yieldsSortReal(sr); }
    bool isRealConst(PTRef tr) const { return isRealConst(getPterm(tr).symb()); }

    bool isNonNegNumConst(PTRef tr) const { return isNumConst(tr) && isNonNegative(getNumConst(tr)); }

    bool isSortInt(SRef sr) const { return sr == getSort_int(); }
    bool isSortReal(SRef sr) const { return sr == getSort_real(); }
    bool isSortNum(SRef sr) const { return isSortInt(sr) or isSortReal(sr); }

    bool yieldsSortInt(SymRef sr) const { return isSortInt(sym_store[sr].rsort()); }
    bool yieldsSortInt(PTRef tr) const { return yieldsSortInt(getPterm(tr).symb()); }
    bool yieldsSortReal(SymRef sr) const { return isSortReal(sym_store[sr].rsort()); }
    bool yieldsSortReal(PTRef tr) const { return yieldsSortReal(getPterm(tr).symb()); }
    bool yieldsSortNum(SymRef sr) const { return yieldsSortInt(sr) or yieldsSortReal(sr); }
    bool yieldsSortNum(PTRef tr) const { return yieldsSortInt(tr) or yieldsSortReal(tr); }

    Number const & getNumConst(PTRef tr) const;

    bool isUFEquality(PTRef tr) const override { return !isNumEq(tr) && Logic::isUFEquality(tr); }
    bool isAtom(PTRef tr) const override {
        return isNumEq(tr) || isLt(tr) || isGt(tr) || isLeq(tr) || isGeq(tr) || Logic::isAtom(tr);
    }
    char const * getDefaultValue(PTRef tr) const override;
    PTRef getDefaultValuePTRef(SRef sref) const override;

    SymRef get_sym_Int_TIMES() const { return sym_Int_TIMES; }
    SymRef get_sym_Real_TIMES() const { return sym_Real_TIMES; }
    SymRef get_sym_Int_TIMES_LIN() const { return sym_Int_TIMES_LIN; }
    SymRef get_sym_Real_TIMES_LIN() const { return sym_Real_TIMES_LIN; }
    SymRef get_sym_Int_TIMES_NONLIN() const { return sym_Int_TIMES_NONLIN; }
    SymRef get_sym_Real_TIMES_NONLIN() const { return sym_Real_TIMES_NONLIN; }
    SymRef get_sym_Int_DIV() const { return sym_Int_DIV; }
    SymRef get_sym_Int_MOD() const { return sym_Int_MOD; }
    SymRef get_sym_Real_DIV() const { return sym_Real_DIV; }
    SymRef get_sym_Int_MINUS() const { return sym_Int_MINUS; }
    SymRef get_sym_Real_MINUS() const { return sym_Real_MINUS; }
    SymRef get_sym_Real_PLUS() const { return sym_Real_PLUS; }
    SymRef get_sym_Int_PLUS() const { return sym_Int_PLUS; }
    SymRef get_sym_Int_NEG() const { return sym_Int_NEG; }
    SymRef get_sym_Int_LEQ() const { return sym_Int_LEQ; }
    SymRef get_sym_Real_LEQ() const { return sym_Real_LEQ; }
    SymRef getLeqForSort(SRef sr) const;
    SymRef get_sym_Int_GEQ() const { return sym_Int_GEQ; }
    SymRef get_sym_Real_GEQ() const { return sym_Real_GEQ; }
    SymRef get_sym_Int_LT() const { return sym_Int_LT; }
    SymRef get_sym_Real_LT() const { return sym_Real_LT; }
    SymRef get_sym_Int_GT() const { return sym_Int_GT; }
    SymRef get_sym_Real_GT() const { return sym_Real_GT; }
    SymRef get_sym_Int_EQ() const { return sym_Int_EQ; }
    SymRef get_sym_Real_EQ() const { return sym_Real_EQ; }
    SymRef get_Sym_Int_ZERO() const { return sym_Int_ZERO; }
    SymRef get_Sym_Real_ZERO() const { return sym_Real_ZERO; }
    SymRef get_Sym_Int_ONE() const { return sym_Int_ONE; }
    SymRef get_Sym_Real_ONE() const { return sym_Real_ONE; }
    SymRef get_sym_Int_ITE() const { return sym_Int_ITE; }
    SymRef get_sym_Real_ITE() const { return sym_Real_ITE; }

    void checkArithSortCompatible(vec<PTRef> const & args, SRef numSort) const {
        for (auto tr : args) {
            if (getSortRef(tr) != numSort) throw ApiException("Argument sorts disagree");
        }
    }

    SRef checkArithSortCompatible(vec<PTRef> const & args) const {
        if (args.size() == 0) { return SRef_Undef; }
        SRef numSort = getSortRef(args[0]);
        checkArithSortCompatible(args, numSort);
        return numSort;
    }
    void checkHasReals() const {
        if (not hasReals()) throw ApiException("Reals not defined for logic");
    }
    void checkHasIntegers() const {
        if (not hasIntegers()) throw ApiException("Integers not defined for logic");
    }

    bool isPlus(SymRef sr) const { return isIntPlus(sr) or isRealPlus(sr); }
    bool isPlus(PTRef tr) const { return isPlus(getPterm(tr).symb()); }
    bool isIntPlus(PTRef tr) const { return isIntPlus(getPterm(tr).symb()); }
    bool isRealPlus(PTRef tr) const { return isRealPlus(getPterm(tr).symb()); }
    bool isIntPlus(SymRef sr) const { return sr == sym_Int_PLUS; }
    bool isRealPlus(SymRef sr) const { return sr == sym_Real_PLUS; }

    bool isMinus(SymRef sr) const { return isIntMinus(sr) or isRealMinus(sr); }
    bool isIntMinus(PTRef tr) const { return isIntMinus(getPterm(tr).symb()); }
    bool isRealMinus(PTRef tr) const { return isRealMinus(getPterm(tr).symb()); }
    bool isIntMinus(SymRef sr) const { return sr == sym_Int_MINUS; }
    bool isRealMinus(SymRef sr) const { return sr == sym_Real_MINUS; }

    bool isNeg(SymRef sr) const { return isIntNeg(sr) or isRealNeg(sr); }
    bool isNeg(PTRef tr) const { return isNeg(getPterm(tr).symb()); }
    bool isIntNeg(PTRef tr) const { return isIntNeg(getPterm(tr).symb()); }
    bool isRealNeg(PTRef tr) const { return isRealNeg(getPterm(tr).symb()); }
    bool isIntNeg(SymRef sr) const { return sr == sym_Int_NEG; }
    bool isRealNeg(SymRef sr) const { return sr == sym_Real_NEG; }

    bool isTimes(SymRef sr) const { return isTimesLin(sr) or isTimesNonlin(sr) or isIntTimes(sr) or isRealTimes(sr); };
    bool isTimesLinOrNonlin(SymRef sr) const { return isTimesLin(sr) or isTimesNonlin(sr); };
    bool isTimesLin(SymRef sr) const { return isIntTimesLin(sr) or isRealTimesLin(sr); }
    bool isTimesNonlin(SymRef sr) const { return isIntTimesNonlin(sr) or isRealTimesNonlin(sr); }
    bool isTimes(PTRef tr) const { return isTimes(getPterm(tr).symb()); }
    bool isTimesLinOrNonlin(PTRef tr) const { return isTimesLinOrNonlin(getPterm(tr).symb()); };
    bool isTimesLin(PTRef tr) const { return isTimesLin(getPterm(tr).symb()); }
    bool isTimesNonlin(PTRef tr) const { return isTimesNonlin(getPterm(tr).symb()); }
    bool isIntTimesLin(PTRef tr) const { return isIntTimesLin(getPterm(tr).symb()); }
    bool isIntTimesNonlin(PTRef tr) const { return isIntTimesNonlin(getPterm(tr).symb()); }
    bool isRealTimesLin(PTRef tr) const { return isRealTimesLin(getPterm(tr).symb()); }
    bool isRealTimesNonlin(PTRef tr) const { return isRealTimesNonlin(getPterm(tr).symb()); }
    bool isIntTimesLin(SymRef sr) const { return sr == sym_Int_TIMES_LIN; }
    bool isIntTimesNonlin(SymRef sr) const { return sr == sym_Int_TIMES_NONLIN; }
    bool isRealTimesLin(SymRef sr) const { return sr == sym_Real_TIMES_LIN; }
    bool isRealTimesNonlin(SymRef sr) const { return sr == sym_Real_TIMES_NONLIN; }
    bool isIntTimes(SymRef sr) const { return sr == sym_Int_TIMES; }
    bool isRealTimes(SymRef sr) const { return sr == sym_Real_TIMES; }

    bool isRealDiv(PTRef tr) const { return isRealDiv(getPterm(tr).symb()); }
    bool isRealDiv(SymRef sr) const { return sr == sym_Real_DIV; }

    bool isIntDiv(PTRef tr) const { return isIntDiv(getPterm(tr).symb()); }
    bool isIntDiv(SymRef sr) const { return sr == sym_Int_DIV; }

    bool isMod(SymRef sr) const { return sr == sym_Int_MOD; }

    bool isNumEq(SymRef sr) const { return isEquality(sr) and isSortNum(sym_store[sr][0]); }
    bool isNumEq(PTRef tr) const { return isNumEq(getPterm(tr).symb()); }
    bool isIntEq(PTRef tr) const { return isIntEq(getPterm(tr).symb()); }
    bool isRealEq(PTRef tr) const { return isRealEq(getPterm(tr).symb()); }
    bool isIntEq(SymRef sr) const { return isEquality(sr) && sym_store[sr][0] == sort_INT; }
    bool isRealEq(SymRef sr) const { return isEquality(sr) && sym_store[sr][0] == sort_REAL; }

    bool isLeq(SymRef sr) const { return isRealLeq(sr) or isIntLeq(sr); }
    bool isLeq(PTRef tr) const { return isLeq(getPterm(tr).symb()); }
    bool isIntLeq(PTRef tr) const { return isIntLeq(getPterm(tr).symb()); }
    bool isRealLeq(PTRef tr) const { return isRealLeq(getPterm(tr).symb()); }
    bool isIntLeq(SymRef sr) const { return sr == sym_Int_LEQ; }
    bool isRealLeq(SymRef sr) const { return sr == sym_Real_LEQ; }

    bool isLt(SymRef sr) const { return isIntLt(sr) or isRealLt(sr); }
    bool isLt(PTRef tr) const { return isLt(getPterm(tr).symb()); }
    bool isIntLt(PTRef tr) const { return isIntLt(getPterm(tr).symb()); }
    bool isRealLt(PTRef tr) const { return isRealLt(getPterm(tr).symb()); }
    bool isIntLt(SymRef sr) const { return sr == sym_Int_LT; }
    bool isRealLt(SymRef sr) const { return sr == sym_Real_LT; }

    bool isGeq(SymRef sr) const { return isIntGeq(sr) or isRealGeq(sr); }
    bool isGeq(PTRef tr) const { return isGeq(getPterm(tr).symb()); }
    bool isIntGeq(PTRef tr) const { return isIntGeq(getPterm(tr).symb()); }
    bool isRealGeq(PTRef tr) const { return isRealGeq(getPterm(tr).symb()); }
    bool isIntGeq(SymRef sr) const { return sr == sym_Int_GEQ; }
    bool isRealGeq(SymRef sr) const { return sr == sym_Real_GEQ; }

    bool isGt(SymRef sr) const { return isIntGt(sr) or isRealGt(sr); }
    bool isGt(PTRef tr) const { return isGt(getPterm(tr).symb()); }
    bool isIntGt(PTRef tr) const { return isIntGt(getPterm(tr).symb()); }
    bool isRealGt(PTRef tr) const { return isRealGt(getPterm(tr).symb()); }
    bool isIntGt(SymRef sr) const { return sr == sym_Int_GT; }
    bool isRealGt(SymRef sr) const { return sr == sym_Real_GT; }

    bool isNumVar(SymRef sr) const { return isVar(sr) and (yieldsSortInt(sr) or yieldsSortReal(sr)); }
    bool isNumVar(PTRef tr) const { return isNumVar(getPterm(tr).symb()); }
    bool isMonomial(PTRef tr) const {
        SymRef sr = getPterm(tr).symb();
        return yieldsSortNum(sr) and not isPlus(sr) and not isTimesLin(sr) and not isNumConst(sr);
    }

    bool isZero(SymRef sr) const { return isIntZero(sr) or isRealZero(sr); }
    bool isZero(PTRef tr) const { return isZero(getSymRef(tr)); }
    bool isIntZero(PTRef tr) const { return tr == getTerm_IntZero(); }
    bool isRealZero(PTRef tr) const { return tr == getTerm_RealZero(); }
    bool isIntZero(SymRef sr) const { return sr == sym_Int_ZERO; }
    bool isRealZero(SymRef sr) const { return sr == sym_Real_ZERO; }

    bool isOne(PTRef tr) const { return isIntOne(tr) or isRealOne(tr); }
    bool isIntOne(PTRef tr) const { return tr == getTerm_IntOne(); }
    bool isMinusOne(PTRef tr) const { return isIntMinusOne(tr) or isRealMinusOne(tr); }
    bool isIntMinusOne(PTRef tr) const { return tr == getTerm_IntMinusOne(); }
    bool isRealOne(PTRef tr) const { return tr == getTerm_RealOne(); }
    bool isRealMinusOne(PTRef tr) const { return tr == getTerm_RealMinusOne(); }
    bool isIntOne(SymRef sr) const { return sr == sym_Int_ONE; }
    bool isRealOne(SymRef sr) const { return sr == sym_Real_ONE; }

    // Real terms are of form c, a, or (* c a) where c is a constant and a is a variable or Ite.
    bool isNumTerm(PTRef tr) const;

    PTRef getTerm_IntZero() const { return term_Int_ZERO; }
    PTRef getTerm_RealZero() const { return term_Real_ZERO; }
    PTRef getTerm_IntOne() const { return term_Int_ONE; }
    PTRef getTerm_RealOne() const { return term_Real_ONE; }
    PTRef getTerm_IntMinusOne() const { return term_Int_MINUSONE; }
    PTRef getTerm_RealMinusOne() const { return term_Real_MINUSONE; }

    void checkSortInt(PTRef tr) {
        if (getSortRef(tr) != getSort_int()) throw ApiException("Expected integral sort");
    }
    void checkSortReal(PTRef tr) {
        if (getSortRef(tr) != getSort_real()) throw ApiException("Expected real sort");
    }
    void checkSortInt(vec<PTRef> const & args) {
        if (args.size() > 0) checkSortInt(args[0]);
    }
    void checkSortReal(vec<PTRef> const & args) {
        if (args.size() > 0) checkSortReal(args[0]);
    }

    SymRef getPlusForSort(SRef sort) const;
    SymRef getTimesLinForSort(SRef sort) const;
    SymRef getTimesNonlinForSort(SRef sort) const;
    SymRef getMinusForSort(SRef sort) const;

    PTRef getZeroForSort(SRef sort) const;
    PTRef getOneForSort(SRef sort) const;
    PTRef getMinusOneForSort(SRef sort) const;

    // Negation
    PTRef mkNeg(PTRef tr);

    // Minus
    PTRef mkMinus(vec<PTRef> &&);
    PTRef mkMinus(PTRef a1, PTRef a2) { return mkMinus(vec<PTRef>({a1, a2})); }
    PTRef mkMinus(vec<PTRef> const & args) {
        vec<PTRef> tmp;
        args.copyTo(tmp);
        return mkMinus(std::move(tmp));
    }

    // Plus
    PTRef mkPlus(vec<PTRef> &&);
    PTRef mkPlus(PTRef p1, PTRef p2) { return mkPlus(vec<PTRef>({p1, p2})); }
    PTRef mkPlus(vec<PTRef> const & args) {
        vec<PTRef> tmp;
        args.copyTo(tmp);
        return mkPlus(std::move(tmp));
    }
    PTRef mkPlus(std::vector<PTRef> const & args) { return mkPlus(vec<PTRef>(args)); }

    // Times
    PTRef mkTimes(vec<PTRef> && args);
    PTRef mkTimes(PTRef p1, PTRef p2) { return mkTimes(vec<PTRef>{p1, p2}); }
    PTRef mkTimes(vec<PTRef> const & args) {
        vec<PTRef> tmp;
        args.copyTo(tmp);
        return mkTimes(std::move(tmp));
    }
    PTRef mkTimes(std::vector<PTRef> const & args) { return mkTimes(vec<PTRef>(args)); }

    // Div
    PTRef mkIntDiv(vec<PTRef> && args);
    PTRef mkIntDiv(PTRef nom, PTRef den) { return mkIntDiv(vec<PTRef>{nom, den}); }
    PTRef mkIntDiv(vec<PTRef> const & args) {
        vec<PTRef> tmp;
        args.copyTo(tmp);
        return mkIntDiv(std::move(tmp));
    }

    PTRef mkRealDiv(vec<PTRef> && args);
    PTRef mkRealDiv(PTRef nom, PTRef den) { return mkRealDiv(vec<PTRef>{nom, den}); }
    PTRef mkRealDiv(vec<PTRef> const & args) {
        vec<PTRef> tmp;
        args.copyTo(tmp);
        return mkRealDiv(std::move(tmp));
    }

    // Mod
    PTRef mkMod(vec<PTRef> && args);
    PTRef mkMod(PTRef first, PTRef second) { return mkMod(vec<PTRef>{first, second}); }

    // Leq
    PTRef mkLeq(vec<PTRef> const & args);
    PTRef mkLeq(PTRef arg1, PTRef arg2) { return mkBinaryLeq(arg1, arg2); }

    // Geq
    PTRef mkGeq(vec<PTRef> const & args);
    PTRef mkGeq(PTRef arg1, PTRef arg2) { return mkBinaryGeq(arg1, arg2); }

    // Lt
    PTRef mkLt(vec<PTRef> const & args);
    PTRef mkLt(PTRef arg1, PTRef arg2) { return mkBinaryLt(arg1, arg2); }

    // Gt
    PTRef mkGt(vec<PTRef> const & args);
    PTRef mkGt(PTRef arg1, PTRef arg2) { return mkBinaryGt(arg1, arg2); }

    bool isLinearTerm(PTRef tr) const;
    bool isLinearFactor(PTRef tr) const;
    pair<Number, vec<PTRef>> getConstantAndFactors(PTRef sum) const;
    // Given a term `t` is splits the term into monomial and its coefficient
    pair<PTRef, PTRef> splitPolyTerm(PTRef term) const;
    PTRef normalizeMul(PTRef mul);
    // Given a sum term 't' returns a normalized inequality 'c <= s' equivalent to '0 <= t'
    PTRef sumToNormalizedInequality(PTRef sum);
    PTRef sumToNormalizedEquality(PTRef sum);
    lbool arithmeticElimination(vec<PTRef> const & top_level_arith, SubstMap & substitutions);

    pair<lbool, SubstMap> retrieveSubstitutions(vec<PtAsgn> const & facts) override;
    void termSort(vec<PTRef> & v) const override;

    PTRef removeAuxVars(PTRef) override;

    std::string printTerm_(PTRef tr, bool ext, bool s) const override;

    // Helper methods

    // Given an inequality 'c <= t', return the constant c; checked version
    PTRef getConstantFromLeq(PTRef);
    // Given an inequality 'c <= t', return the term t; checked version
    PTRef getTermFromLeq(PTRef);
    // Given an inequality 'c <= t', return the pair <c,t> for a constant c and term t; unchecked version, for
    // internal use
    std::pair<PTRef, PTRef> leqToConstantAndTerm(PTRef);

    // MB: In pure LA, there are never nested boolean terms
    vec<PTRef> getNestedBoolRoots(PTRef) const override { return vec<PTRef>(); }

protected:
    friend class LessThan_deepPTRef;

    PTRef mkBinaryLeq(PTRef lhs, PTRef rhs);
    PTRef mkBinaryGeq(PTRef lhs, PTRef rhs) { return mkBinaryLeq(rhs, lhs); }
    PTRef mkBinaryLt(PTRef lhs, PTRef rhs) { return mkNot(mkBinaryGeq(lhs, rhs)); }
    PTRef mkBinaryGt(PTRef lhs, PTRef rhs) { return mkNot(mkBinaryLeq(lhs, rhs)); }
    SymRef declareFun_Multiplication_LinNonlin(std::string const & s, SRef rsort, vec<SRef> const & args) {
        return sym_store.newInternalSymb(s.c_str(), rsort, args, SymConf::CommutativeNoScopingLeftAssoc);
    }
    PTRef mkBinaryEq(PTRef lhs, PTRef rhs) override;
    pair<Number, PTRef> sumToNormalizedPair(PTRef sum);
    pair<Number, PTRef> sumToNormalizedIntPair(PTRef sum);
    pair<Number, PTRef> sumToNormalizedRealPair(PTRef sum);

    bool hasNegativeLeadingVariable(PTRef poly) const;

    std::vector<Number *> numbers;

    static std::string const e_nonlinear_term;

    static std::string const tk_val_int_default;
    static std::string const tk_val_real_default;
    static std::string const tk_real_zero;
    static std::string const tk_int_zero;
    static std::string const tk_real_one;
    static std::string const tk_int_one;
    static std::string const tk_real_neg;
    static std::string const tk_int_neg;
    static std::string const tk_real_minus;
    static std::string const tk_int_minus;
    static std::string const tk_real_plus;
    static std::string const tk_int_plus;
    static std::string const tk_real_times;
    static std::string const tk_int_times;
    static std::string const tk_real_div;
    static std::string const tk_int_div;
    static std::string const tk_int_mod;
    static std::string const tk_real_leq;
    static std::string const tk_int_leq;
    static std::string const tk_real_lt;
    static std::string const tk_int_lt;
    static std::string const tk_real_geq;
    static std::string const tk_int_geq;
    static std::string const tk_real_gt;
    static std::string const tk_int_gt;
    static std::string const s_sort_real;
    static std::string const s_sort_int;

    // Reals
    SRef sort_REAL;
    PTRef term_Real_ZERO;
    PTRef term_Real_ONE;
    PTRef term_Real_MINUSONE;

    SymRef sym_Real_ZERO;
    SymRef sym_Real_ONE;
    SymRef sym_Real_NEG;
    SymRef sym_Real_MINUS;
    SymRef sym_Real_PLUS;
    SymRef sym_Real_TIMES;
    SymRef sym_Real_TIMES_LIN;
    SymRef sym_Real_TIMES_NONLIN;
    SymRef sym_Real_DIV;
    SymRef sym_Real_EQ;
    SymRef sym_Real_LEQ;
    SymRef sym_Real_LT;
    SymRef sym_Real_GEQ;
    SymRef sym_Real_GT;
    SymRef sym_Real_ITE;
    SymRef sym_Real_DISTINCT;

    // Integers
    SRef sort_INT;
    PTRef term_Int_ZERO;
    PTRef term_Int_ONE;
    PTRef term_Int_MINUSONE;
    SymRef sym_Int_ZERO;
    SymRef sym_Int_ONE;
    SymRef sym_Int_NEG;
    SymRef sym_Int_MINUS;
    SymRef sym_Int_PLUS;
    SymRef sym_Int_TIMES;
    SymRef sym_Int_TIMES_LIN;
    SymRef sym_Int_TIMES_NONLIN;
    SymRef sym_Int_DIV;
    SymRef sym_Int_MOD;
    SymRef sym_Int_EQ;
    SymRef sym_Int_LEQ;
    SymRef sym_Int_LT;
    SymRef sym_Int_GEQ;
    SymRef sym_Int_GT;
    SymRef sym_Int_ITE;
    SymRef sym_Int_DISTINCT;
};

// Determine for two multiplicative terms (* k1 v1) and (* k2 v2), v1 !=
// v2 which one is smaller, based on the PTRef of v1 and v2.  (i.e.
// v1.ptref <  v2.ptref iff (* k1 v1) < (* k2 v2)).
//
// This code is required for canonicalising the terms and correctly identifying their sign.
//
// If term contains a const-ite:
//   (* ite v) or (* ite c) or (* v ite) or (* c ite)  => consider {v,c}.ptref
//   (* ite1 ite2) => consider min(ite1.ptref, ite2.ptref)
class LessThan_deepPTRef {
public:
    LessThan_deepPTRef(ArithLogic const & l) : l(l) {}

    bool operator()(PTRef x_, PTRef y_) const;

private:
    ArithLogic const & l;
    uint32_t getVarIdFromProduct(PTRef term) const;
};

} // namespace opensmt

#endif
