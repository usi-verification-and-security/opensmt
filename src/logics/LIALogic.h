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
    virtual bool isBuiltinSort(SRef sr) const override;// { return sr == sort_INTEGER || Logic::isBuiltinSort(sr); }
    virtual bool  isNonnegNumConst(PTRef tr) const override;// { return isNumConst(tr) && getNumConst(tr) >= 0; }
    virtual SRef   getSort_num()  const override;// {return sort_INTEGER;}

    bool        isIntPlus(SymRef sr)  const;// { return sr == sym_Int_PLUS; }
    bool        isNumPlus(PTRef tr)   const override;// { return isIntPlus(getPterm(tr).symb()); }
    bool        isIntMinus(SymRef sr) const;// { return sr == sym_Int_MINUS; }
    bool        isNumMinus(PTRef tr)  const override;// { return isIntMinus(getPterm(tr).symb()); }
    bool        isIntNeg(SymRef sr)   const;// { return sr == sym_Int_NEG; }
    bool        isNumNeg(PTRef tr)    const override;// { return isIntNeg(getPterm(tr).symb()); }
    bool        isIntTimes(SymRef sr) const;// { return sr == sym_Int_TIMES; }
    bool        isNumTimes(PTRef tr)  const override;// { return isIntTimes(getPterm(tr).symb()); }
    bool        isIntDiv(SymRef sr)   const;// { return sr == sym_Int_DIV; }
    bool        isNumDiv(PTRef tr)    const override ;//{ return isIntDiv(getPterm(tr).symb()); }
    bool        isIntEq(SymRef sr)    const;// { return isEquality(sr) && (sym_store[sr][0] == sort_INTEGER); }
    bool        isNumEq(PTRef tr)     const override;// { return isIntEq(getPterm(tr).symb()); }
    bool        isIntLeq(SymRef sr)   const;// { return sr == sym_Int_LEQ; }
    bool        isNumLeq(PTRef tr)    const override;// { return isIntLeq(getPterm(tr).symb()); }
    bool        isIntLt(SymRef sr)    const;// { return sr == sym_Int_LT; }
    bool        isNumLt(PTRef tr)     const override;// { return isIntLt(getPterm(tr).symb()); }
    bool        isIntGeq(SymRef sr)   const;// { return sr == sym_Int_GEQ; }
    bool        isNumGeq(PTRef tr)    const override;// { return isIntGeq(getPterm(tr).symb()); }
    bool        isIntGt(SymRef sr)    const;// { return sr == sym_Int_GT; }
    bool        isNumGt(PTRef tr)     const override;// { return isIntGt(getPterm(tr).symb()); }
    bool        isIntVar(SymRef sr)   const;// { return isVar(sr) && sym_store[sr].rsort() == sort_INTEGER; }
    bool        isNumVar(PTRef tr)    const override;// { return isIntVar(getPterm(tr).symb());}
    bool        isIntZero(SymRef sr)  const;// { return sr == sym_Int_ZERO; }
    bool        isNumZero(PTRef tr)   const override;// { return tr == term_Int_ZERO; }
    bool        isIntOne(SymRef sr)   const;// { return sr == sym_Int_ONE; }
    bool        isNumOne(PTRef tr)    const override ;//{ return tr == term_Int_ONE; }

    bool        hasSortInt(SymRef sr) const;// { return sym_store[sr].rsort() == sort_INTEGER; }
    bool        hasSortNum(PTRef tr) const override ;//{ return hasSortInt(getPterm(tr).symb()); }

    PTRef       getTerm_NumZero() const override;// { return term_Int_ZERO; }
    PTRef       getTerm_NumOne()  const override;// { return term_Int_ONE; }
    PTRef       getTerm_NumMinusOne()  const override;// { return term_Int_ONE; }

    virtual const SymRef get_sym_Num_TIMES () const override;
    virtual const SymRef get_sym_Num_DIV () const override;
    virtual const SymRef get_sym_Num_MINUS () const override;
    virtual const SymRef get_sym_Num_PLUS () const override;
    virtual const SymRef get_sym_Num_NEG () const override;
    virtual const SymRef get_sym_Num_LEQ () const override;
    virtual const SymRef get_sym_Num_GEQ () const override;
    virtual const SymRef get_sym_Num_LT () const override;
    virtual const SymRef get_sym_Num_GT () const override;
    virtual const SymRef get_sym_Num_EQ () const override;
    virtual const SymRef get_sym_Num_ZERO () const override;
    virtual const SymRef get_sym_Num_ONE () const override;
    virtual const SymRef get_sym_Num_ITE () const override;
    virtual const SRef get_sort_NUM () const override;
};

#endif