#ifndef LIALOGIC_H
#define LIALOGIC_H
#include "Logic.h"
#include "Integer.h"
#include "LALogic.h"

class LIALogic: public LALogic
{
protected:
    vec<opensmt::Integer2*> integers;//PS. replace this with Number?
    SymRef              sym_Int_ZERO;
    SymRef              sym_Int_ONE;
    SymRef              sym_Int_NEG;
    SymRef              sym_Int_MINUS;
    SymRef              sym_Int_PLUS;
    SymRef              sym_Int_TIMES;
    SymRef              sym_Int_DIV;
    SymRef              sym_Int_MOD;
    SymRef              sym_Int_ABS;
    SymRef              sym_Int_EQ;
    SymRef              sym_Int_LEQ;
    SymRef              sym_Int_LT;
    SymRef              sym_Int_GEQ;
    SymRef              sym_Int_GT;
    SymRef              sym_Int_ITE;
    SRef                sort_INTEGER;
    PTRef               term_Int_ZERO;
    PTRef               term_Int_ONE;
    PTRef               term_Int_MINUSONE;
    static const char*  tk_int_zero;
    static const char*  tk_int_one;
    static const char*  tk_int_neg;
    static const char*  tk_int_minus;
    static const char*  tk_int_plus;
    static const char*  tk_int_times;
    static const char*  tk_int_div;
    static const char*  tk_int_mod;
    static const char*  tk_int_abs;
    static const char*  tk_int_leq;
    static const char*  tk_int_lt;
    static const char*  tk_int_geq;
    static const char*  tk_int_gt;
    static const char*  s_sort_integer;
    static const char*  e_nonlinear_term;
    bool split_eq;

public:
    LIALogic();
    ~LIALogic () {
        for (int i = 0; i < integers.size(); i++) delete integers[i];
    }
    virtual const char*   getName()         const override { return "QF_LIA"; }
    virtual const opensmt::Logic_t getLogic() const override { return opensmt::Logic_t::QF_LIA; }
    virtual SRef   getSort_num()  const override { return sort_INTEGER; }
    bool        isBuiltinFunction(SymRef sr) const override { return isIntDiv(sr) || isIntMod(sr) || LALogic::isBuiltinFunction(sr); }

    bool        isIntPlus(SymRef sr)  const { return sr == sym_Int_PLUS; }
    bool        isIntMinus(SymRef sr) const { return sr == sym_Int_MINUS; }
    bool        isIntNeg(SymRef sr)   const { return sr == sym_Int_NEG; }
    bool        isIntTimes(SymRef sr) const { return sr == sym_Int_TIMES; }
    bool        isIntDiv(SymRef sr)   const { return sr == sym_Int_DIV; }
    bool        isIntMod(SymRef sr)   const { return sr == sym_Int_MOD; }
    bool        isIntAbs(SymRef sr)   const { return sr == sym_Int_ABS; }
    bool        isIntEq(SymRef sr)    const { return isEquality(sr) && (sym_store[sr][0] == sort_INTEGER); }
    bool        isIntLeq(SymRef sr)   const { return sr == sym_Int_LEQ; }
    bool        isIntLt(SymRef sr)    const { return sr == sym_Int_LT; }
    bool        isIntGeq(SymRef sr)   const { return sr == sym_Int_GEQ; }
    bool        isIntGt(SymRef sr)    const { return sr == sym_Int_GT; }
    bool        isIntVar(SymRef sr)   const { return isVar(sr) && sym_store[sr].rsort() == sort_INTEGER; }
    bool        isIntZero(SymRef sr)  const { return sr == sym_Int_ZERO; }
    bool        isIntOne(SymRef sr)   const { return sr == sym_Int_ONE; }
    bool        isNumVarLike(SymRef tr) const override { return LALogic::isNumVarLike(tr) || isIntDiv(tr) || isIntMod(tr); }

    bool        hasSortInt(SymRef sr) const { return sym_store[sr].rsort() == sort_INTEGER; }

    PTRef       getTerm_NumZero() const override { return term_Int_ZERO; }
    PTRef       getTerm_NumOne()  const override { return term_Int_ONE; }
    PTRef       getTerm_NumMinusOne() const override { return term_Int_MINUSONE; }

    virtual const SymRef get_sym_Num_TIMES () const override { return sym_Int_TIMES; }
    virtual const SymRef get_sym_Num_MINUS () const override { return sym_Int_MINUS; }
    virtual const SymRef get_sym_Num_PLUS () const override { return sym_Int_PLUS; }
    virtual const SymRef get_sym_Num_NEG () const override { return sym_Int_NEG; }
    virtual const SymRef get_sym_Num_LEQ () const override { return sym_Int_LEQ; }
    virtual const SymRef get_sym_Num_GEQ () const override { return sym_Int_GEQ; }
    virtual const SymRef get_sym_Num_LT () const override { return sym_Int_LT; }
    virtual const SymRef get_sym_Num_GT () const override { return sym_Int_GT; }
    virtual const SymRef get_sym_Num_EQ () const override { return sym_Int_EQ; }
    virtual const SymRef get_sym_Num_ZERO () const override { return sym_Int_ZERO; }
    virtual const SymRef get_sym_Num_ONE () const override { return sym_Int_ONE; }
    virtual const SymRef get_sym_Num_ITE () const override { return sym_Int_ITE; }
    const SymRef get_sym_Int_DIV() const { return sym_Int_DIV; }
    const SymRef get_sym_Int_MOD() const { return sym_Int_MOD; }
    const SymRef get_sym_Int_ABS() const { return sym_Int_ABS; }
    virtual const SRef get_sort_Num () const override { return sort_INTEGER; }

    PTRef mkNumDiv(vec<PTRef> const& args) override { return mkIntDiv(args); }
    PTRef mkNumDiv(PTRef dividend, PTRef divisor) override { return mkIntDiv(dividend, divisor); }
    PTRef mkIntMod(vec<PTRef> const & args);
    PTRef mkIntMod(PTRef first, PTRef second);
    PTRef mkIntDiv(vec<PTRef> const & args);
    PTRef mkIntDiv(PTRef dividend, PTRef divisor);

    PTRef insertTerm (SymRef sym, vec<PTRef>& terms) override;
    virtual PTRef sumToNormalizedInequality(PTRef sum) override;

private:
    PTRef _mkIntMod(vec<PTRef> const & args);
    PTRef _mkIntDiv(vec<PTRef> const & args);
};

#endif