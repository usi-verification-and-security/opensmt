/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2015 Antti Hyvarinen

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
#ifndef LRALOGIC_H
#define LRALOGIC_H
#include "Logic.h"
#include "LALogic.h"
#include "Real.h"
class LRANonLinearException : std::logic_error
{
public:
    LRANonLinearException(const char* reason_) : std::logic_error(reason_) {
    }
    LRANonLinearException(std::string const & reason) : std::logic_error(reason) {
    }
    ~LRANonLinearException() = default;
};
class LRALogic: public LALogic
{
protected:
    vec<opensmt::Real*> reals;
    SymRef              sym_Real_ZERO;
    SymRef              sym_Real_ONE;
    SymRef              sym_Real_NEG;
    SymRef              sym_Real_MINUS;
    SymRef              sym_Real_PLUS;
    SymRef              sym_Real_TIMES;
    SymRef              sym_Real_DIV;
    SymRef              sym_Real_EQ;
    SymRef              sym_Real_LEQ;
    SymRef              sym_Real_LT;
    SymRef              sym_Real_GEQ;
    SymRef              sym_Real_GT;
    SymRef              sym_Real_ITE;
    SRef                sort_REAL;
    PTRef               term_Real_ZERO;
    PTRef               term_Real_ONE;
    //static const char*  tk_val_real_default;
    static const char*  tk_real_zero;
    static const char*  tk_real_one;
    static const char*  tk_real_neg;
    static const char*  tk_real_minus;
    static const char*  tk_real_plus;
    static const char*  tk_real_times;
    static const char*  tk_real_div;
    static const char*  tk_real_leq;
    static const char*  tk_real_lt;
    static const char*  tk_real_geq;
    static const char*  tk_real_gt;
    static const char*  s_sort_real;
    static const char*  e_nonlinear_term;
    bool split_eq;

public:
    LRALogic                    (SMTConfig& c);
    ~LRALogic                   () {
        for (int i = 0; i < reals.size(); i++) delete reals[i];
        if (config.sat_split_type() != spt_none)
            cerr << "; Num of LRA equalities in input: " << la_split_inequalities.getSize()/2 << "\n";
    }
    virtual const char*   getName()              const override { return "QF_LRA"; }
    virtual const opensmt::Logic_t getLogic()    const override { return opensmt::Logic_t::QF_LRA; }

    virtual bool isBuiltinSort  (SRef sr) const override { return sr == sort_REAL || Logic::isBuiltinSort(sr); }
    virtual bool  isNonnegNumConst (PTRef tr)    const override { return isNumConst(tr) && getNumConst(tr) >= 0; }
    SRef        getSort_num    ()              const override { return sort_REAL;}

    bool        isRealPlus(SymRef sr) const { return sr == sym_Real_PLUS; }
    bool        isNumPlus(PTRef tr) const override { return isRealPlus(getPterm(tr).symb()); }
    bool        isRealMinus(SymRef sr) const { return sr == sym_Real_MINUS; }
    bool        isNumMinus(PTRef tr) const override { return isRealMinus(getPterm(tr).symb()); }
    bool        isRealNeg(SymRef sr) const { return sr == sym_Real_NEG; }
    bool        isNumNeg(PTRef tr) const override { return isRealNeg(getPterm(tr).symb()); }
    bool        isRealTimes(SymRef sr) const { return sr == sym_Real_TIMES; }
    bool        isNumTimes(PTRef tr) const override { return isRealTimes(getPterm(tr).symb()); }
    bool        isRealDiv(SymRef sr) const { return sr == sym_Real_DIV; }
    bool        isNumDiv(PTRef tr) const override { return isRealDiv(getPterm(tr).symb());  }
    bool        isRealEq(SymRef sr) const { return isEquality(sr) && (sym_store[sr][0] == sort_REAL); }
    bool        isNumEq(PTRef tr) const override { return isRealEq(getPterm(tr).symb()); }
    bool        isRealLeq(SymRef sr) const { return sr == sym_Real_LEQ; }
    bool        isNumLeq(PTRef tr) const override { return isRealLeq(getPterm(tr).symb()); }
    bool        isRealLt(SymRef sr) const { return sr == sym_Real_LT; }
    bool        isNumLt(PTRef tr) const override { return isRealLt(getPterm(tr).symb());  }
    bool        isRealGeq(SymRef sr) const { return sr == sym_Real_GEQ; }
    bool        isNumGeq(PTRef tr) const override { return isRealGeq(getPterm(tr).symb()); }
    bool        isRealGt(SymRef sr) const { return sr == sym_Real_GT; }
    bool        isNumGt(PTRef tr) const override { return isRealGt(getPterm(tr).symb()); }
    bool        isRealVar(SymRef sr) const { return isVar(sr) && sym_store[sr].rsort() == sort_REAL; }
    bool        isNumVar(PTRef tr) const override {return isRealVar(getPterm(tr).symb());}
    bool        isRealZero(SymRef sr) const { return sr == sym_Real_ZERO; }
    bool        isNumZero(PTRef tr) const override { return tr == term_Real_ZERO; }
    bool        isRealOne(SymRef sr) const { return sr == sym_Real_ONE; }
    bool        isNumOne(PTRef tr) const override { return tr == term_Real_ONE; }

    // Real terms are of form c, a, or (* c a) where c is a constant and
    // a is a variable.

    bool        hasSortReal(SymRef sr) const { return sym_store[sr].rsort() == sort_REAL; }
    bool        hasSortNum(PTRef tr) const override;

    PTRef       getTerm_NumZero() const override;
    PTRef       getTerm_NumOne()  const override;

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