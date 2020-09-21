/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2017 Antti Hyvarinen

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
#ifndef CUFLOGIC_H
#define CUFLOGIC_H
#include "Logic.h"

class CUFLogic: public Logic
{
  protected:
    Map<PTRef,bool,PTRefHash> comm_eqs;         // a+b <-> b+a
    Map<PTRef,bool,PTRefHash> diseq_eqs;        // a>b -> a != b
    Map<PTRef,bool,PTRefHash> diseq_split;      // a != b -> (a>b) || (a<b)
    Map<PTRef,bool,PTRefHash> mod_ineqs;        // b > 0 -> 0 <= a % b < b, b < 0 -> b < a % b <= 0
    Map<PTRef,bool,PTRefHash> inc_diseqs;       // a++ != a (< is not safe for overflows for some compiler semantics)
    Map<PTRef,bool,PTRefHash> compl_diseqs;     // ~a != a

  public:
    void getCommEqs(vec<PTRef>& out) const { comm_eqs.getKeys(out); }

  protected:
    SymRef              sym_CUF_ZERO;   // 0
    SymRef              sym_CUF_ONE;    // 1
    SymRef              sym_CUF_NEG;    // -
    SymRef              sym_CUF_MINUS;  // -
    SymRef              sym_CUF_PLUS;   // +
    SymRef              sym_CUF_TIMES;  // *
    SymRef              sym_CUF_DIV;    // /
//    SymRef              sym_CUF_EQ;     // ==
    SymRef              sym_CUF_LEQ;    // <=
    SymRef              sym_CUF_LT;     // <
    SymRef              sym_CUF_GEQ;    // >=
    SymRef              sym_CUF_GT;     // >
    SymRef              sym_CUF_LSHIFT; // <<
    SymRef              sym_CUF_LRSHIFT; // l>>
    SymRef              sym_CUF_ARSHIFT; // a>>
    SymRef              sym_CUF_MOD;    // %
    SymRef              sym_CUF_BWAND;  // &
    SymRef              sym_CUF_BWOR;   // |
    SymRef              sym_CUF_INC;    // ++
    SymRef              sym_CUF_DEC;    // --
    SymRef              sym_CUF_NEQ;    // !=
    SymRef              sym_CUF_LAND;   // &&
    SymRef              sym_CUF_LOR;    // ||
//    SymRef              sym_CUF_NOT;    // !
    SymRef              sym_CUF_BWXOR;  // ^
    SymRef              sym_CUF_COMPL;  // ~
    SymRef              sym_CUF_SIZEOF; // sizeof
    SymRef              sym_CUF_ADDROF; // &
    SymRef              sym_CUF_PTR;    // *
 //   SymRef              sym_CUF_COND;   // ?

    SRef                sort_CUFNUM;
    SRef                sort_CUFSTR;

    PTRef               term_CUF_ZERO;
    PTRef               term_CUF_ONE;

    static int tk_cuf_zero;
    static int tk_cuf_one;
    static const char*  tk_cuf_neg;
    static const char*  tk_cuf_minus;
    static const char*  tk_cuf_plus;
    static const char*  tk_cuf_times;
    static const char*  tk_cuf_div;
    static const char*  tk_cuf_leq;
    static const char*  tk_cuf_lt;
    static const char*  tk_cuf_geq;
    static const char*  tk_cuf_gt;
    static const char*  tk_cuf_lshift;
    static const char*  tk_cuf_lrshift;
    static const char*  tk_cuf_arshift;
    static const char*  tk_cuf_mod;
    static const char*  tk_cuf_bwand;
    static const char*  tk_cuf_bwor;
    static const char*  tk_cuf_inc;
    static const char*  tk_cuf_dec;
    static const char*  tk_cuf_neq;
    static const char*  tk_cuf_land;
    static const char*  tk_cuf_lor;
    static const char*  tk_cuf_not;
    static const char*  tk_cuf_bwxor;
    static const char*  tk_cuf_compl;
    static const char*  tk_cuf_sizeof;
    static const char*  tk_cuf_addrof;
    static const char*  tk_cuf_ptr;
    static const char*  tk_cuf_cond;

    static const char*  s_sort_cufnum;
    static const char*  s_sort_cufstr;

  public:
    CUFLogic();
    ~CUFLogic();
    virtual const char*   getName() const override { return "QF_CUF"; }
    virtual const opensmt::Logic_t getLogic() const override { return opensmt::Logic_t::QF_CUF; }

//    virtual PTRef         insertTerm(SymRef sym, vec<PTRef>& terms, char** msg);
    using Logic::mkConst;
    virtual PTRef         mkConst   (const int c) { return mkCUFConst(c); }
    PTRef                 mkCUFConst   (const int c) { std::string num = std::to_string(c); PTRef tr = Logic::mkConst(sort_CUFNUM, num.c_str()); return tr; }
    virtual PTRef         mkCUFNumVar(const char* name) { return mkVar(sort_CUFNUM, name); }
    virtual bool          isBuiltinSort(SRef sr) const override { return (sr == sort_CUFNUM) || (sr == sort_CUFSTR) || Logic::isBuiltinSort(sr); }
    virtual bool          isBuiltinConstant(SymRef sr) const override { return isCUFNUMConst(sr) || Logic::isBuiltinConstant(sr); }

    PTRef conjoinExtras(PTRef root) override;

    bool isCUFNUMConst(SymRef sr) const { return isConstant(sr) && hasSortCUFNUM(sr); }
    bool isCUFNUMConst(PTRef tr)  const { return isCUFNUMConst(getPterm(tr).symb()); }
    bool hasSortCUFNUM(const SymRef sr) const { return getSortRef(sr) == sort_CUFNUM; }
    bool hasSortCUFNUM(const PTRef tr)  const { return hasSortCUFNUM(getPterm(tr).symb()); }

    SRef declareSort_CUFNUM(char** msg);
    SRef getSort_CUFNUM() const { return sort_CUFNUM; }
    const int getCUFNUMConst(PTRef tr) const;


    bool isCUFPlus(SymRef sr)   const { return sr == sym_CUF_PLUS; }
    bool isCUFPlus(PTRef tr)    const { return isCUFPlus(getPterm(tr).symb()); }
    bool isCUFMinus(SymRef sr)  const { return sr == sym_CUF_MINUS; }
    bool isCUFMinus(PTRef tr)   const { return isCUFMinus(getPterm(tr).symb()); }
    bool isCUFNeg(SymRef sr)    const { return sr == sym_CUF_NEG; }
    bool isCUFNeg(PTRef tr)     const { return isCUFNeg(getPterm(tr).symb()); }
    bool isCUFTimes(SymRef sr)  const { return sr == sym_CUF_TIMES; }
    bool isCUFTimes(PTRef tr)   const { return isCUFTimes(getPterm(tr).symb()); }
    bool isCUFDiv(SymRef sr)    const { return sr == sym_CUF_DIV; }
    bool isCUFDiv(PTRef tr)     const { return isCUFDiv(getPterm(tr).symb()); }
    bool isCUFEq(SymRef sr)     const { return isEquality(sr) && (sym_store[sr][0] == sort_CUFNUM); }
    bool isCUFEq(PTRef tr)      const { return isCUFEq(getPterm(tr).symb()); }
    bool isCUFLeq(SymRef sr)    const { return sr == sym_CUF_LEQ; }
    bool isCUFLeq(PTRef tr)     const { return isCUFLeq(getPterm(tr).symb()); }
    bool isCUFLt(SymRef sr)     const { return sr == sym_CUF_LT; }
    bool isCUFLt(PTRef tr)      const { return isCUFLt(getPterm(tr).symb()); }
    bool isCUFGeq(SymRef sr)    const { return sr == sym_CUF_GEQ; }
    bool isCUFGeq(PTRef tr)     const { return isCUFGeq(getPterm(tr).symb()); }
    bool isCUFGt(SymRef sr)     const { return sr == sym_CUF_GT; }
    bool isCUFGt(PTRef tr)      const { return isCUFGt(getPterm(tr).symb()); }
    bool isCUFVar(SymRef sr)    const { return isVar(sr) && sym_store[sr].rsort() == sort_CUFNUM; }
    bool isCUFVar(PTRef tr)     const { return isCUFVar(getPterm(tr).symb()); }
    bool isCUFZero(SymRef sr)   const { return sr == sym_CUF_ZERO; }
    bool isCUFZero(PTRef tr)    const { return tr == term_CUF_ZERO; }
    bool isCUFOne(SymRef sr)    const { return sr == sym_CUF_ONE; }
    bool isCUFOne(PTRef tr)     const { return tr == term_CUF_ONE; }
    bool isCUFLshift(SymRef sr) const { return sr == sym_CUF_LSHIFT; }
    bool isCUFLshift(PTRef tr)  const { return isCUFLshift(getPterm(tr).symb()); }
    bool isCUFLRshift(SymRef sr) const { return sr == sym_CUF_LRSHIFT; }
    bool isCUFLRshift(PTRef tr)  const { return isCUFLRshift(getPterm(tr).symb()); }
    bool isCUFARshift(SymRef sr) const { return sr == sym_CUF_ARSHIFT; }
    bool isCUFARshift(PTRef tr)  const { return isCUFARshift(getPterm(tr).symb()); }
    bool isCUFMod(SymRef sr)    const { return sr == sym_CUF_MOD; }
    bool isCUFMod(PTRef tr)     const { return isCUFMod(getPterm(tr).symb()); }
    bool isCUFBwAnd(SymRef sr)  const { return sr == sym_CUF_BWAND; }
    bool isCUFBwAnd(PTRef tr)   const { return isCUFBwAnd(getPterm(tr).symb()); }
    bool isCUFBwOr(SymRef sr)   const { return sr == sym_CUF_BWOR; }
    bool isCUFBwOr(PTRef tr)    const { return isCUFBwOr(getPterm(tr).symb()); }
    bool isCUFInc(SymRef sr)    const { return sr == sym_CUF_INC; }
    bool isCUFInc(PTRef tr)     const { return isCUFInc(getPterm(tr).symb()); }
    bool isCUFDec(SymRef sr)    const { return sr == sym_CUF_DEC; }
    bool isCUFDec(PTRef tr)     const { return isCUFDec(getPterm(tr).symb()); }
    bool isCUFNeq(SymRef sr)    const { return sr == sym_CUF_NEQ; }
    bool isCUFNeq(PTRef tr)     const { return isCUFNeq(getPterm(tr).symb()); }
    bool isCUFLand(SymRef sr)   const { return sr == sym_CUF_LAND; }
    bool isCUFLand(PTRef tr)    const { return isCUFLand(getPterm(tr).symb()); }
    bool isCUFLor(SymRef sr)    const { return sr == sym_CUF_LOR; }
    bool isCUFLor(PTRef tr)     const { return isCUFLor(getPterm(tr).symb()); }
//    bool isCUFNot(SymRef sr)    const { return sr == sym_CUF_NOT; }
//    bool isCUFNot(PTRef tr)     const { return isCUFNot(getPterm(tr).symb()); }
    bool isCUFBwxor(SymRef sr)  const { return sr == sym_CUF_BWXOR; }
    bool isCUFBwxor(PTRef tr)   const { return isCUFBwxor(getPterm(tr).symb()); }
    bool isCUFCompl(SymRef sr)  const { return sr == sym_CUF_COMPL; }
    bool isCUFCompl(PTRef tr)   const { return isCUFCompl(getPterm(tr).symb()); }
    bool isCUFSizeof(SymRef sr) const { return sr == sym_CUF_SIZEOF; }
    bool isCUFSizeof(PTRef tr)  const { return isCUFSizeof(getPterm(tr).symb()); }
    bool isCUFAddrof(SymRef sr) const { return sr == sym_CUF_ADDROF; }
    bool isCUFAddrof(PTRef tr)  const { return isCUFAddrof(getPterm(tr).symb()); }
    bool isCUFPtr(SymRef sr)    const { return sr == sym_CUF_PTR; }
    bool isCUFPtr(PTRef tr)     const { return isCUFPtr(getPterm(tr).symb()); }
//    bool isCUFCond(SymRef sr)   const { return sr == sym_CUF_COND; }
//    bool isCUFCond(PTRef tr)    const { return isCUFCond(getPterm(tr).symb()); }

    bool isUFEquality(PTRef tr) const override { return !isCUFEq(tr) && Logic::isUFEquality(tr); }
    bool isTheoryEquality(PTRef tr) const override { return isCUFEq(tr); }
    bool isUF(PTRef tr) const override { return !hasSortCUFNUM(tr) && Logic::isUF(tr); }

    PTRef getTerm_CUFZero() { return term_CUF_ZERO; }
    PTRef getTerm_CUFOne()  { return term_CUF_ONE; }

    PTRef mkCUFNeg(const vec<PTRef>& args) { assert(args.size() == 1); return mkCUFNeg(args[0]); }
    PTRef mkCUFNeg(PTRef, char**);
    PTRef mkCUFNeg(PTRef tr) {char* msg; PTRef trn = mkCUFNeg(tr, &msg); assert(trn != PTRef_Undef); return trn; }

    //PTRef mkCUFMinus(const vec<PTRef>& args) { assert(args.size() == 2); return mkCUFMinus(args[0], args[1]); }
    PTRef mkCUFMinus(const vec<PTRef>&, char**);
    PTRef mkCUFMinus(const vec<PTRef>& args) { char *msg; PTRef tr = mkCUFMinus(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef mkCUFMinus(const PTRef a1, const PTRef a2) { vec<PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkCUFMinus(tmp); }

    PTRef mkCUFPlus(const vec<PTRef>& args) { assert(args.size() == 2); return mkCUFPlus(args[0], args[1]); }
    PTRef mkCUFPlus(const PTRef arg1, const PTRef arg2, char**);
    PTRef mkCUFPlus(const PTRef arg1, const PTRef arg2) { char *msg; PTRef tr = mkCUFPlus(arg1, arg2, &msg); assert(tr != PTRef_Undef); return tr; }

    PTRef mkCUFTimes(const vec<PTRef>& args) {assert(args.size() == 2); return mkCUFTimes(args[0], args[1]);}
    PTRef mkCUFTimes(const PTRef, const PTRef, char**);
    PTRef mkCUFTimes(const PTRef arg1, const PTRef arg2) { char *msg; PTRef tr = mkCUFTimes(arg1, arg2, &msg); assert(tr != PTRef_Undef); return tr; }

    PTRef mkCUFDiv(const vec<PTRef>& args) {assert(args.size() == 2); return mkCUFDiv(args[0], args[1]);}
    PTRef mkCUFDiv(const PTRef nom, const PTRef den);

    PTRef mkCUFLeq(const vec<PTRef>& args) {assert(args.size() == 2); char *msg; return mkCUFLeq(args[0], args[1], &msg);}
    PTRef mkCUFLeq(const PTRef arg1, const PTRef arg2, char**);

    PTRef mkCUFGeq(const vec<PTRef>& args) {assert(args.size() == 2); char *msg; return mkCUFGeq(args[0], args[1], &msg);}
    PTRef mkCUFGeq(const PTRef arg1, const PTRef arg2, char**);

    PTRef mkCUFLt(const vec<PTRef>& args) {assert(args.size() == 2); char *msg; return mkCUFLt(args[0], args[1], &msg);}
    PTRef mkCUFLt(const PTRef arg1, const PTRef arg2, char** tmp);

    PTRef mkCUFGt(const vec<PTRef>& args) {assert(args.size() == 2); char *msg; return mkCUFGt(args[0], args[1], &msg);}
    PTRef mkCUFGt(const PTRef arg1, const PTRef arg2, char** tmp);

    PTRef mkCUFLshift(const vec<PTRef>& args) {assert(args.size() == 2); return mkCUFLshift(args[0], args[1]);}
    PTRef mkCUFLshift   (const PTRef, const PTRef);

    PTRef mkCUFLRshift(const vec<PTRef>& args) {assert(args.size() == 2); return mkCUFLRshift(args[0], args[1]);}
    PTRef mkCUFLRshift(const PTRef, const PTRef);
    PTRef mkCUFARshift(const vec<PTRef>& args) {assert(args.size() == 2); return mkCUFARshift(args[0], args[1]);}
    PTRef mkCUFARshift(const PTRef, const PTRef);

    PTRef mkCUFMod(const vec<PTRef>& args) {assert(args.size() == 2); return mkCUFMod(args[0], args[1]);}
    PTRef mkCUFMod      (const PTRef, const PTRef);

    PTRef mkCUFBwAnd(const vec<PTRef>& args) {assert(args.size() == 2); return mkCUFBwAnd(args[0], args[1]);}
    PTRef mkCUFBwAnd    (const PTRef, const PTRef);

    PTRef mkCUFBwOr(const vec<PTRef>& args) {assert(args.size() == 2); return mkCUFBwOr(args[0], args[1]);}
    PTRef mkCUFBwOr     (const PTRef, const PTRef);

    PTRef mkCUFInc(const vec<PTRef>& args) {assert(args.size() == 1);  return mkCUFInc(args[0]);}
    PTRef mkCUFInc      (const PTRef);

    PTRef mkCUFDec(const vec<PTRef>& args) {assert(args.size() == 1);  return mkCUFDec(args[0]);}
    PTRef mkCUFDec      (const PTRef);

    PTRef mkCUFNeq(const vec<PTRef>& args) {assert(args.size() == 2); return mkCUFNeq(args[0], args[1]);}
    PTRef mkCUFNeq      (const PTRef, const PTRef);

    PTRef mkCUFLand(const vec<PTRef>& args) {assert(args.size() == 2); return mkCUFLand(args[0], args[1]);}
    PTRef mkCUFLand     (const PTRef, const PTRef);

    PTRef mkCUFLor(const vec<PTRef>& args) {assert(args.size() == 2); return mkCUFLor(args[0], args[1]);}
    PTRef mkCUFLor      (const PTRef, const PTRef);

    PTRef mkCUFNot(const vec<PTRef>& args) {assert(args.size() == 1); return mkCUFNot(args[0]);}
    PTRef mkCUFNot      (const PTRef);

    PTRef mkCUFBwXor(const vec<PTRef>& args) {assert(args.size() == 2); return mkCUFBwXor(args[0], args[1]);}
    PTRef mkCUFBwXor    (const PTRef, const PTRef);

    PTRef mkCUFCompl(const vec<PTRef>& args) {assert(args.size() == 1); return mkCUFCompl(args[0]);}
    PTRef mkCUFCompl    (const PTRef);

    PTRef mkCUFSizeof(const vec<PTRef>& args) {assert(args.size() == 1); return mkCUFSizeof(args[0]);}
    PTRef mkCUFSizeof   (const PTRef);

    PTRef mkCUFAddrof(const vec<PTRef>& args) {assert(args.size() == 1); return mkCUFAddrof(args[0]);}
    PTRef mkCUFAddrof   (const PTRef);

    PTRef mkCUFPtr(const vec<PTRef>& args) {assert(args.size() == 1); return mkCUFPtr(args[0]);}
    PTRef mkCUFPtr      (const PTRef);

    PTRef mkCUFCond(const vec<PTRef>& args) {assert(args.size() == 3); return mkCUFCond(args[0], args[1], args[2]);}
    PTRef mkCUFCond     (const PTRef, const PTRef, const PTRef);

};
#endif
