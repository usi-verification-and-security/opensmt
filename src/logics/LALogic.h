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
    PTRef            insertTerm       (SymRef sym, vec<PTRef>& terms) override;
    virtual SRef     getSort_num      () const;
    PTRef            mkConst          (const char* name, const char **msg) override;
    PTRef            mkConst          (SRef s, const char* name) override;
    virtual PTRef    mkConst          (const opensmt::Number& c);
    virtual PTRef    mkConst          (const char* num);
    virtual PTRef    mkNumVar         (const char* name);
    bool             isBuiltinSort    (SRef sr) const override;
    bool             isBuiltinConstant(SymRef sr) const override;

    virtual bool  isNumConst     (SymRef sr)     const;
    virtual bool  isNumConst     (PTRef tr)      const;
    virtual bool  isNonnegNumConst (PTRef tr)  const;
    virtual bool   hasSortNum(SymRef sr) const;
    virtual bool   hasSortNum(PTRef tr)  const;
    virtual const opensmt::Number& getNumConst(PTRef tr) const;
    bool           isUFEquality(PTRef tr) const override;
    bool           isTheoryEquality(PTRef tr) const override;
    bool           isAtom(PTRef tr) const override;
    bool           isUF(PTRef tr) const override;
    bool           isUF(SymRef sr) const override;
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
    virtual const SRef get_sort_NUM () const =0;

    bool isNumPlus(SymRef sr) const;
    virtual bool isNumPlus(PTRef tr) const;
    bool isNumMinus(SymRef sr) const;
    virtual bool isNumMinus(PTRef tr) const ;
    bool isNumNeg(SymRef sr) const ;
    virtual bool isNumNeg(PTRef tr) const ;
    bool isNumTimes(SymRef sr) const;
    virtual bool isNumTimes(PTRef tr) const ;
    bool isNumDiv(SymRef sr) const;
    virtual bool isNumDiv(PTRef tr) const;
    bool isNumEq(SymRef sr) const ;
    virtual bool isNumEq(PTRef tr) const ;
    bool isNumLeq(SymRef sr) const;
    virtual bool isNumLeq(PTRef tr) const ;
    bool isNumLt(SymRef sr) const;
    virtual bool isNumLt(PTRef tr) const;
    bool isNumGeq(SymRef sr) const;
    virtual bool isNumGeq(PTRef tr) const;
    bool isNumGt(SymRef sr) const ;
    virtual bool isNumGt(PTRef tr) const;
    bool isNumVar(SymRef sr) const;
    virtual bool isNumVar(PTRef tr) const;
    bool isNumVarOrIte(SymRef sr) const;
    virtual bool isNumVarOrIte(PTRef tr) const;
    bool isNumZero(SymRef sr) const;
    virtual bool isNumZero(PTRef tr) const;
    bool isNumOne(SymRef sr) const;
    virtual bool isNumOne(PTRef tr) const;
    // Real terms are of form c, a, or (* c a) where c is a constant and a is a variable or Ite.
    virtual bool isNumTerm(PTRef tr) const;

    virtual PTRef getTerm_NumZero() const = 0;
    virtual PTRef getTerm_NumOne() const = 0;
    virtual PTRef getTerm_NumMinusOne() const = 0;
    virtual PTRef mkNumNeg(PTRef, char **);
    virtual PTRef mkNumNeg(PTRef tr);
    virtual PTRef mkNumMinus(const vec<PTRef> &, char **);
    virtual PTRef mkNumMinus(const vec<PTRef> &args);
    virtual PTRef mkNumMinus(const PTRef a1, const PTRef a2);
    virtual PTRef mkNumPlus(const vec<PTRef> &, char **);
    virtual PTRef mkNumPlus(const vec<PTRef> &args);
    virtual PTRef mkNumPlus(const std::vector<PTRef> &args);
    virtual PTRef mkNumPlus(const PTRef p1, const PTRef p2);
    virtual PTRef mkNumTimes(const vec<PTRef> &, char **);
    virtual PTRef mkNumTimes(const vec<PTRef> &args);
    virtual PTRef mkNumTimes(const PTRef p1, const PTRef p2);
    virtual PTRef mkNumTimes(const std::vector<PTRef> &args);
    virtual PTRef mkNumDiv(const vec<PTRef> &args);
    virtual PTRef mkNumDiv(const PTRef nom, const PTRef den);
    virtual PTRef mkNumLeq(const vec<PTRef> &args);
    virtual PTRef mkNumLeq(const PTRef arg1, const PTRef arg2);
    virtual PTRef mkNumGeq(const vec<PTRef> & args);
    virtual PTRef mkNumGeq(const PTRef arg1, const PTRef arg2);
    virtual PTRef mkNumLt(const vec<PTRef> & args);
    virtual PTRef mkNumLt(const PTRef arg1, const PTRef arg2);
    virtual PTRef mkNumGt(const vec<PTRef> & args);
    virtual PTRef mkNumGt(const PTRef arg1, const PTRef arg2);

    virtual bool isNegated(PTRef tr) const;
    virtual bool isLinearTerm(PTRef tr) const;
    virtual bool isLinearFactor(PTRef tr) const;
    virtual void splitTermToVarAndConst(const PTRef &term, PTRef &var, PTRef &fac) const;
    virtual PTRef normalizeSum(PTRef sum);
    virtual PTRef normalizeMul(PTRef mul);
    // Given a sum term 't' returns a normalized inequality 'c <= s' equivalent to '0 <= t'
    virtual PTRef sumToNormalizedInequality(PTRef sum);
    virtual lbool arithmeticElimination(const vec<PTRef> & top_level_arith,
                                        Map<PTRef, PtAsgn, PTRefHash> & substitutions);

    lbool retrieveSubstitutions(const vec<PtAsgn> &facts, Map<PTRef, PtAsgn, PTRefHash> &substs) override;
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