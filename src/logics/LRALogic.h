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
#include "SMTConfig.h"

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
    PTRef               term_Real_MINUSONE;
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
    LRALogic();
    ~LRALogic () {
        for (int i = 0; i < reals.size(); i++) delete reals[i];
    }
    virtual const char* getName() const override { return "QF_LRA"; }
    virtual const opensmt::Logic_t getLogic() const override { return opensmt::Logic_t::QF_LRA; }
    bool        isBuiltinFunction(SymRef sr) const override { return isRealDiv(sr) || LALogic::isBuiltinFunction(sr); }
    SRef        getSort_num() const override { return sort_REAL;}

    bool        isRealPlus(SymRef sr) const { return sr == sym_Real_PLUS; }
    bool        isRealMinus(SymRef sr) const { return sr == sym_Real_MINUS; }
    bool        isRealNeg(SymRef sr) const { return sr == sym_Real_NEG; }
    bool        isRealTimes(SymRef sr) const { return sr == sym_Real_TIMES; }
    bool        isRealDiv(SymRef sr) const { return sr == sym_Real_DIV; }
    bool        isRealEq(SymRef sr) const { return isEquality(sr) && (sym_store[sr][0] == sort_REAL); }
    bool        isRealLeq(SymRef sr) const { return sr == sym_Real_LEQ; }
    bool        isRealLt(SymRef sr) const { return sr == sym_Real_LT; }
    bool        isRealGeq(SymRef sr) const { return sr == sym_Real_GEQ; }
    bool        isRealGt(SymRef sr) const { return sr == sym_Real_GT; }
    bool        isRealVar(SymRef sr) const { return isVar(sr) && sym_store[sr].rsort() == sort_REAL; }
    bool        isRealZero(SymRef sr) const { return sr == sym_Real_ZERO; }
    bool        isRealOne(SymRef sr) const { return sr == sym_Real_ONE; }

    // Real terms are of form c, a, or (* c a) where c is a constant and
    // a is a variable.

    bool        hasSortReal(SymRef sr) const { return sym_store[sr].rsort() == sort_REAL; }

    PTRef       getTerm_NumZero() const override { return term_Real_ZERO; }
    PTRef       getTerm_NumOne()  const override { return term_Real_ONE; }
    PTRef       getTerm_NumMinusOne()  const override { return term_Real_MINUSONE; }

    virtual const SymRef get_sym_Num_TIMES () const override { return sym_Real_TIMES; }
    virtual const SymRef get_sym_Num_DIV () const override { return sym_Real_DIV; }
    virtual const SymRef get_sym_Num_MINUS () const override { return sym_Real_MINUS; }
    virtual const SymRef get_sym_Num_PLUS () const override { return sym_Real_PLUS; }
    virtual const SymRef get_sym_Num_NEG () const override { return sym_Real_NEG; }
    virtual const SymRef get_sym_Num_LEQ () const override { return sym_Real_LEQ; }
    virtual const SymRef get_sym_Num_GEQ () const override { return sym_Real_GEQ; }
    virtual const SymRef get_sym_Num_LT () const override { return sym_Real_LT; }
    virtual const SymRef get_sym_Num_GT () const override { return sym_Real_GT; }
    virtual const SymRef get_sym_Num_EQ () const override { return sym_Real_EQ; }
    virtual const SymRef get_sym_Num_ZERO () const override { return sym_Real_ZERO; }
    virtual const SymRef get_sym_Num_ONE () const override { return sym_Real_ONE; }
    virtual const SymRef get_sym_Num_ITE () const override { return sym_Real_ITE; }
    virtual const SRef get_sort_Num () const override { return sort_REAL; }

    const SymRef get_sym_Real_DIV () const { return sym_Real_DIV; }

    PTRef mkNumDiv(vec<PTRef> const& args) override { return mkRealDiv(args); }
    PTRef mkNumDiv(PTRef dividend, PTRef divisor) override { return mkRealDiv(dividend, divisor); }
    PTRef mkRealDiv(vec<PTRef> const&);
    PTRef mkRealDiv(PTRef dividend, PTRef divisor) { return mkRealDiv({dividend, divisor}); }

    PTRef insertTerm(SymRef sym, vec<PTRef> &terms) override;

};

#endif