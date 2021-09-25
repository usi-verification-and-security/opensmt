#ifndef LALOGIC_H
#define LALOGIC_H
#include "Logic.h"
#include "Number.h"
class LANonLinearException : std::runtime_error
{
public:
    LANonLinearException(const char* reason_) : runtime_error(reason_) {
    }
    virtual const char* what() const noexcept
    {
        char* out;
        int chars_written = asprintf(&out, "Term %s is non-linear", std::runtime_error::what());
        assert(chars_written >= 0);
        (void) chars_written;
        return out;
    }
    ~LANonLinearException() = default;
};

class LADivisionByZeroException : public std::runtime_error
{
public:
    LADivisionByZeroException() : runtime_error("Explicit division by zero encountered!") {}
    ~LADivisionByZeroException() = default;
};

class LALogic: public Logic
{
protected:
    vec<opensmt::Number*> numbers;

    static const char*  tk_val_num_default;
    static const char *tk_num_zero;
    static const char *tk_num_one;
    static const char *tk_num_neg;
    static const char *tk_num_minus;
    static const char *tk_num_plus;
    static const char *tk_num_times;
    static const char *tk_num_div;
    static const char *tk_num_leq;
    static const char *tk_num_lt;
    static const char *tk_num_geq;
    static const char *tk_num_gt;
    static const char*  s_sort_num;

public:
    LALogic() = default;
    ~LALogic() { for(int i = 0; i < numbers.size(); ++i) {delete numbers[i];}}
    bool             isBuiltinFunction(SymRef sr) const override;
    using Logic::insertTerm;
    PTRef            insertTerm       (SymRef sym, vec<PTRef>&& terms) override;
    virtual SRef     getSort_num      () const = 0;
    PTRef            mkConst          (const char* name, const char **msg) override;
    PTRef            mkConst          (SRef s, const char* name) override;
    virtual PTRef    mkConst          (const opensmt::Number& c);
    virtual PTRef    mkConst          (const char* num) { return mkConst(getSort_num(), num); }
    virtual PTRef    mkNumVar         (const char* name) { return mkVar(getSort_num(), name); }
    bool             isBuiltinSort    (SRef sr) const override { return sr == get_sort_Num() || Logic::isBuiltinSort(sr); }
    bool             isBuiltinConstant(SymRef sr) const override { return (isNumConst(sr) || Logic::isBuiltinConstant(sr)); }

    bool isNumConst (SymRef sr) const { return Logic::isConstant(sr) && hasSortNum(sr); }
    bool isNumConst (PTRef tr)  const { return isNumConst(getPterm(tr).symb()); }
    bool isNonnegNumConst (PTRef tr) const { return isNumConst(tr) && getNumConst(tr) >= 0; }
    bool hasSortNum(SymRef sr) const { return sym_store[sr].rsort() == get_sort_Num(); }
    bool hasSortNum(PTRef tr)  const { return hasSortNum(getPterm(tr).symb()); }
    virtual const opensmt::Number& getNumConst(PTRef tr) const;

    bool           isUFEquality(PTRef tr) const override { return !isNumEq(tr) && Logic::isUFEquality(tr); }
    bool           isTheoryEquality(PTRef tr) const override { return isNumEq(tr); }
    bool           isAtom(PTRef tr) const override { return isNumEq(tr) || isNumLt(tr) || isNumGt(tr) || isNumLeq(tr) || isNumGeq(tr) || Logic::isAtom(tr); }
    bool           isUF(PTRef tr) const override { return isUF(term_store[tr].symb()); }
    bool           isUF(SymRef sr) const override { return !sym_store[sr].isInterpreted(); }
    const char*    getDefaultValue(const PTRef tr) const override;
    PTRef          getDefaultValuePTRef(const SRef sref) const override;


    virtual const SymRef get_sym_Num_TIMES () const =0;
    virtual const SymRef get_sym_Num_DIV () const =0;
    virtual const SymRef get_sym_Num_MINUS () const =0;
    virtual const SymRef get_sym_Num_PLUS () const =0;
    virtual const SymRef get_sym_Num_NEG () const =0;
    virtual const SymRef get_sym_Num_LEQ () const =0;
    virtual const SymRef get_sym_Num_GEQ () const =0;
    virtual const SymRef get_sym_Num_LT () const =0;
    virtual const SymRef get_sym_Num_GT () const =0;
    virtual const SymRef get_sym_Num_EQ () const =0;
    virtual const SymRef get_sym_Num_ZERO () const =0;
    virtual const SymRef get_sym_Num_ONE () const =0;
    virtual const SymRef get_sym_Num_ITE () const =0;
    virtual const SRef   get_sort_Num () const =0;

    bool isNumPlus(SymRef sr) const { return sr == get_sym_Num_PLUS(); }
    bool isNumPlus(PTRef tr) const { return isNumPlus(getPterm(tr).symb()); }
    bool isNumMinus(SymRef sr) const { return sr == get_sym_Num_MINUS(); }
    bool isNumMinus(PTRef tr) const { return isNumMinus(getPterm(tr).symb()); }
    bool isNumNeg(SymRef sr) const { return sr == get_sym_Num_NEG(); }
    bool isNumNeg(PTRef tr) const { return isNumNeg(getPterm(tr).symb()); }
    bool isNumTimes(SymRef sr) const { return sr == get_sym_Num_TIMES(); }
    bool isNumTimes(PTRef tr) const { return isNumTimes(getPterm(tr).symb()); }
    bool isNumDiv(SymRef sr) const { return sr == get_sym_Num_DIV(); }
    bool isNumDiv(PTRef tr) const { return isNumDiv(getPterm(tr).symb()); }
    bool isNumEq(SymRef sr) const { return isEquality(sr) && (sym_store[sr][0] == get_sort_Num());}
    bool isNumEq(PTRef tr) const { return isNumEq(getPterm(tr).symb()); }
    bool isNumLeq(SymRef sr) const { return sr == get_sym_Num_LEQ(); }
    bool isNumLeq(PTRef tr) const { return isNumLeq(getPterm(tr).symb()); }
    bool isNumLt(SymRef sr) const { return sr == get_sym_Num_LT(); }
    bool isNumLt(PTRef tr) const { return isNumLt(getPterm(tr).symb()); }
    bool isNumGeq(SymRef sr) const { return sr == get_sym_Num_GEQ(); }
    bool isNumGeq(PTRef tr) const { return isNumGeq(getPterm(tr).symb()); }
    bool isNumGt(SymRef sr) const { return sr == get_sym_Num_GT(); }
    bool isNumGt(PTRef tr) const { return isNumGt(getPterm(tr).symb()); }
    bool isNumVar(SymRef sr) const { return isVar(sr) && sym_store[sr].rsort() == get_sort_Num(); }
    bool isNumVar(PTRef tr) const { return isNumVar(getPterm(tr).symb()); }
    bool isNumVarOrIte(SymRef sr) const { return isNumVar(sr) || isIte(sr); }
    bool isNumVarOrIte(PTRef tr) const { return isNumVarOrIte(getPterm(tr).symb()); }
    virtual bool isNumVarLike(SymRef tr) const { return isNumVarOrIte(tr); }
    bool isNumVarLike(PTRef tr) const { return isNumVarLike(getPterm(tr).symb()); }
    bool isNumZero(SymRef sr) const { return sr == get_sym_Num_ZERO(); }
    bool isNumZero(PTRef tr) const { return tr == getTerm_NumZero(); }
    bool isNumOne(SymRef sr) const { return sr == get_sym_Num_ONE(); }
    bool isNumOne(PTRef tr) const { return tr == getTerm_NumOne(); }

    // Real terms are of form c, a, or (* c a) where c is a constant and a is a variable or Ite.
    virtual bool isNumTerm(PTRef tr) const;

    virtual PTRef getTerm_NumZero() const = 0;
    virtual PTRef getTerm_NumOne() const = 0;
    virtual PTRef getTerm_NumMinusOne() const = 0;

    PTRef mkNumNeg(PTRef tr);

    PTRef mkNumMinus(vec<PTRef> && args);
    PTRef mkNumMinus(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkNumMinus(std::move(tmp)); }
    PTRef mkNumMinus(PTRef a1, PTRef a2) { return mkNumMinus({a1, a2}); }

    PTRef mkNumPlus(vec<PTRef> && args);
    PTRef mkNumPlus(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkNumPlus(std::move(tmp)); }
    PTRef mkNumPlus(std::vector<PTRef> const & args) { return mkNumPlus(vec<PTRef>(args)); }
    PTRef mkNumPlus(PTRef p1, PTRef p2) { return mkNumPlus(vec<PTRef>{p1, p2}); }

    PTRef mkNumTimes(vec<PTRef> && args);
    PTRef mkNumTimes(vec<PTRef> const & args) { vec<PTRef> tmp; args.copyTo(tmp); return mkNumTimes(std::move(tmp)); }
    PTRef mkNumTimes(PTRef p1, PTRef p2) { return mkNumTimes(vec<PTRef>{p1, p2}); }
    PTRef mkNumTimes(std::vector<PTRef> const & args) { return mkNumTimes(vec<PTRef>(args)); }

    virtual PTRef mkNumDiv(vec<PTRef> && args) = 0;
    virtual PTRef mkNumDiv(const PTRef nom, const PTRef den) = 0;

    PTRef mkNumLeq(vec<PTRef> const & args);
    PTRef mkNumLeq(PTRef arg1, PTRef arg2) { return mkBinaryLeq(arg1, arg2); }

    PTRef mkNumGeq(vec<PTRef> const & args);
    PTRef mkNumGeq(PTRef arg1, PTRef arg2) { return mkBinaryGeq(arg1, arg2); }

    PTRef mkNumLt(vec<PTRef> const & args);
    PTRef mkNumLt(PTRef arg1, PTRef arg2) { return mkBinaryLt(arg1, arg2); }

    PTRef mkNumGt(const vec<PTRef> & args);
    PTRef mkNumGt(PTRef arg1, PTRef arg2) { return mkBinaryGt(arg1, arg2); }

    virtual bool isNegated(PTRef tr) const;
    virtual bool isLinearTerm(PTRef tr) const;
    virtual bool isLinearFactor(PTRef tr) const;
    virtual void splitTermToVarAndConst(const PTRef &term, PTRef &var, PTRef &fac) const;
    virtual PTRef normalizeMul(PTRef mul);
    // Given a sum term 't' returns a normalized inequality 'c <= s' equivalent to '0 <= t'
    virtual PTRef sumToNormalizedInequality(PTRef sum);
    virtual lbool arithmeticElimination(const vec<PTRef> & top_level_arith, SubstMap & substitutions);

    opensmt::pair<lbool,SubstMap> retrieveSubstitutions(const vec<PtAsgn> &facts) override;
    void termSort(vec<PTRef> &v) const override;
    char *printTerm_(PTRef tr, bool ext, bool s) const override;
    char *printTerm(PTRef tr) const override;
    char *printTerm(PTRef tr, bool l, bool s) const override;

    // Helper methods

    // Given an inequality 'c <= t', return the constant c; checked version
    PTRef getConstantFromLeq(PTRef);
    // Given an inequality 'c <= t', return the term t; checked version
    PTRef getTermFromLeq(PTRef);
    // Given an inequality 'c <= t', return the pair <c,t> for a constant c and term t; unchecked version, for internal use
    std::pair<PTRef, PTRef> leqToConstantAndTerm(PTRef);

    // MB: In pure LA, there are never nested boolean terms
    vec<PTRef> getNestedBoolRoots (PTRef)  const override { return vec<PTRef>(); }

protected:
    PTRef mkBinaryLeq(PTRef lhs, PTRef rhs);
    PTRef mkBinaryGeq(PTRef lhs, PTRef rhs);
    PTRef mkBinaryLt(PTRef lhs, PTRef rhs);
    PTRef mkBinaryGt(PTRef lhs, PTRef rhs);

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
    const LALogic& l;
    uint32_t getVarIdFromProduct(PTRef term) const;
public:
    LessThan_deepPTRef(const LALogic* l) : l(*l) {}

    bool operator ()  (PTRef x_, PTRef y_) const;

};

class SimplifyConst {
protected:
    LALogic& l;
    PTRef simplifyConstOp(const vec<PTRef> & const_terms);
    virtual void Op(opensmt::Number& s, const opensmt::Number& v) const = 0;
    virtual opensmt::Number getIdOp() const = 0;
    virtual void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const = 0;
public:
    SimplifyConst(LALogic& log) : l(log) {}
    void simplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new);
};

class SimplifyConstSum : public SimplifyConst {
    void Op(opensmt::Number& s, const opensmt::Number& v) const;// { s += v; }
    opensmt::Number getIdOp() const;// { return 0; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
public:
    SimplifyConstSum(LALogic& log) : SimplifyConst(log) {}
};

class SimplifyConstTimes : public SimplifyConst {
    void Op(opensmt::Number& s, const opensmt::Number& v) const;// { s *= v; }
    opensmt::Number getIdOp() const;// { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
public:
    SimplifyConstTimes(LALogic& log) : SimplifyConst(log) {}
};

class SimplifyConstDiv : public SimplifyConst {
    void Op(opensmt::Number& s, const opensmt::Number& v) const;// { if (v == 0) { printf("explicit div by zero\n"); } s /= v; }
    opensmt::Number getIdOp() const;// { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
public:
    SimplifyConstDiv(LALogic& log) : SimplifyConst(log) {}
};
#endif