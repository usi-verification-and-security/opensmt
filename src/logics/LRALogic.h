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

class LRALogic: public Logic
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

    static const char* e_nonlinear_term;

    bool split_eq;
    void visit(PTRef, Map<PTRef,PTRef,PTRefHash>&);
  public:
    LRALogic                  (SMTConfig& c);
    ~LRALogic                 () { for (int i = 0; i < reals.size(); i++) delete reals[i]; }

    PTRef       insertTerm         (SymRef sym, vec<PTRef>& terms, char** msg);

    PTRef       mkConst        (const char* name, const char **msg);
    PTRef       mkConst        (SRef s, const char* name);

    bool        isRealConst    (PTRef tr) { return isConstant(tr) && hasSortReal(tr); }

    PTRef       mkConst         (const opensmt::Real& c) { char* rat; opensmt::stringToRational(rat, c.get_str().c_str()); PTRef tr = mkConst(sort_REAL, rat); free(rat); return tr; }
    SRef        declareSort_Real(char** msg);

    SRef        getSort_real    ()              const { return sort_REAL;    }

    const opensmt::Real& getRealConst(PTRef tr);

    bool        isRealPlus(SymRef sr) const { return sr == sym_Real_PLUS; }
    bool        isRealPlus(PTRef tr) const { return isRealPlus(getPterm(tr).symb()); }
    bool        isRealMinus(SymRef sr) const { return sr == sym_Real_MINUS; }
    bool        isRealMinus(PTRef tr) const { return isRealMinus(getPterm(tr).symb()); }
    bool        isRealNeg(SymRef sr) const { return sr == sym_Real_NEG; }
    bool        isRealNeg(PTRef tr) const { return isRealNeg(getPterm(tr).symb()); }
    bool        isRealTimes(SymRef sr) const { return sr == sym_Real_TIMES; }
    bool        isRealTimes(PTRef tr) const { return isRealTimes(getPterm(tr).symb()); }
    bool        isRealDiv(SymRef sr) const { return sr == sym_Real_DIV; }
    bool        isRealDiv(PTRef tr) const { return isRealDiv(getPterm(tr).symb()); }
    bool        isRealEq(SymRef sr) const { return isEquality(sr) && (sym_store[sr][0] == sort_REAL); }
    bool        isRealEq(PTRef tr) const { return isRealEq(getPterm(tr).symb()); }
    bool        isRealLeq(SymRef sr) const { return sr == sym_Real_LEQ; }
    bool        isRealLeq(PTRef tr) const { return isRealLeq(getPterm(tr).symb()); }
    bool        isRealLt(SymRef sr) const { return sr == sym_Real_LT; }
    bool        isRealLt(PTRef tr) const { return isRealLt(getPterm(tr).symb()); }
    bool        isRealGeq(SymRef sr) const { return sr == sym_Real_GEQ; }
    bool        isRealGeq(PTRef tr) const { return isRealGeq(getPterm(tr).symb()); }
    bool        isRealGt(SymRef sr) const { return sr == sym_Real_GT; }
    bool        isRealGt(PTRef tr) const { return isRealGt(getPterm(tr).symb()); }
    bool        isRealVar(SymRef sr) const { return isVar(sr) && sym_store[sr].rsort() == sort_REAL; }
    bool        isRealVar(PTRef tr) const { return isRealVar(getPterm(tr).symb()); }
    bool        isRealZero(SymRef sr) const { return sr == sym_Real_ZERO; }
    bool        isRealZero(PTRef tr) const { return tr == term_Real_ZERO; }
    bool        isRealOne(SymRef sr) const { return sr == sym_Real_ONE; }
    bool        isRealOne(PTRef tr) const { return tr == term_Real_ONE; }

    // Real terms are of form c, a, or (* c a) where c is a constant and
    // a is a variable.
    bool        isRealTerm(PTRef tr) const;
    bool        hasSortReal(PTRef tr) const { return sym_store[getPterm(tr).symb()].rsort() == sort_REAL; }

    bool        isUFEquality(PTRef tr) const { return !isRealEq(tr) && Logic::isUFEquality(tr); }
    bool        isTheoryEquality(PTRef tr) const { return isRealEq(tr); }

    bool isUF(PTRef tr) const { return !hasSortReal(tr) && Logic::isUF(tr); }

    PTRef       getTerm_RealZero() { return term_Real_ZERO; }
    PTRef       getTerm_RealOne() { return term_Real_ONE; }
    PTRef       mkRealNeg(PTRef, char**);
    PTRef       mkRealNeg(PTRef tr) {char* msg; PTRef trn = mkRealNeg(tr, &msg); assert(trn != PTRef_Undef); return trn; }
    PTRef       mkRealMinus(const vec<PTRef>&, char**);
    PTRef       mkRealMinus(const vec<PTRef>& args) { char *msg; PTRef tr = mkRealMinus(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkRealPlus(const vec<PTRef>&, char**);
    PTRef       mkRealPlus(const vec<PTRef>& args) { char *msg; PTRef tr = mkRealPlus(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkRealTimes(const vec<PTRef>&, char**);
    PTRef       mkRealTimes(const vec<PTRef>& args) { char *msg; PTRef tr = mkRealTimes(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkRealDiv(const vec<PTRef>&, char**);
    PTRef       mkRealDiv(const vec<PTRef>& args) { char *msg; PTRef tr = mkRealDiv(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkRealLeq(const vec<PTRef>&, char**);
    PTRef       mkRealLeq(const vec<PTRef>& args) { char* msg; PTRef tr = mkRealLeq(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef       mkRealLeq(const PTRef arg1, const PTRef arg2) { vec<PTRef> tmp; tmp.push(arg1); tmp.push(arg2); return mkRealLeq(tmp); }
    PTRef       mkRealGeq(const vec<PTRef>&, char**);
    PTRef       mkRealLt(const vec<PTRef>&, char**);
    PTRef       mkRealGt(const vec<PTRef>&, char**);

    void        splitTermToVarAndConst(const PTRef& term, PTRef& var, PTRef& fac);
    PTRef       normalizeSum(PTRef sum); // Use for normalizing leq terms: sort the sum and divide all terms with the first factor
    PTRef       normalizeMul(PTRef mul); // Use for normalizing leq terms of form 0 <= c*v

    // Logic specific simplifications: conjoin Ites, make substitutions
    // and split equalities
//    virtual bool simplify(PTRef root, PTRef& root_out);

    lbool retrieveSubstitutions(vec<PtAsgn>& facts, Map<PTRef,PtAsgn,PTRefHash>& substs);
    lbool arithmeticElimination(vec<PTRef>&, Map<PTRef,PtAsgn,PTRefHash>&);
    void simplifyAndSplitEq(PTRef, PTRef&);

    virtual void serializeLogicData(int*& logicdata_buf) const;
    void deserializeLogicData(const int* logicdata_buf);
};

// Determine for two multiplicative terms (* k1 v1) and (* k2 v2), v1 !=
// v2 which one is smaller, based on the PTRef of v1 and v2.  (i.e.
// v1.ptref <  v2.ptref iff (* k1 v1) < (* k2 v2))
class LessThan_deepPTRef {
    LRALogic& l;
  public:
    LessThan_deepPTRef(LRALogic* l) : l(*l) {}
    bool operator ()  (PTRef& x_, PTRef& y_) {
        PTRef c_x;
        PTRef v_x;
        PTRef c_y;
        PTRef v_y;
        l.splitTermToVarAndConst(x_, v_x, c_x);
        l.splitTermToVarAndConst(y_, v_y, c_y);
        return v_x.x < v_y.x;
    }
};


class SimplifyConst {
  protected:
    LRALogic& l;
    PTRef simplifyConstOp(const vec<PTRef>& const_terms, char** msg);
    virtual void Op(opensmt::Real& s, const opensmt::Real& v) const = 0;
    virtual opensmt::Real getIdOp() const = 0;
    virtual void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const = 0;
  public:
    SimplifyConst(LRALogic& log) : l(log) {}
    void simplify(SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new, char** msg);
};

class SimplifyConstSum : public SimplifyConst {
    void Op(opensmt::Real& s, const opensmt::Real& v) const { s += v; }
    opensmt::Real getIdOp() const { return 0; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
  public:
    SimplifyConstSum(LRALogic& log) : SimplifyConst(log) {}
};

class SimplifyConstTimes : public SimplifyConst {
    void Op(opensmt::Real& s, const opensmt::Real& v) const { s *= v; }
    opensmt::Real getIdOp() const { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
  public:
    SimplifyConstTimes(LRALogic& log) : SimplifyConst(log) {}
};

class SimplifyConstDiv : public SimplifyConst {
    void Op(opensmt::Real& s, const opensmt::Real& v) const { if (v == 0) { printf("explicit div by zero\n"); } s /= v; }
    opensmt::Real getIdOp() const { return 1; }
    void constSimplify(const SymRef& s, const vec<PTRef>& terms, SymRef& s_new, vec<PTRef>& terms_new) const;
  public:
    SimplifyConstDiv(LRALogic& log) : SimplifyConst(log) {}
};


#endif

