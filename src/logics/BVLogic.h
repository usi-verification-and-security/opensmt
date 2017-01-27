/*******************************************************************\
Module: New Logic for BitVector

 *  Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Author: Sepideh Asadi <sepideh.a65@gmail.com>
 *  Created on: Jan 16, 2017
\*******************************************************************/
#ifndef BVLOGIC_H
#define BVLOGIC_H
#include "Logic.h"
#include "CUFLogic.h"


class BVLogic: public CUFLogic
{
//  protected:
//    Map<PTRef,bool,PTRefHash> comm_eqs;         // a+b <-> b+a
//    Map<PTRef,bool,PTRefHash> diseq_eqs;        // a>b -> a != b
//    Map<PTRef,bool,PTRefHash> diseq_split;      // a != b -> (a>b) || (a<b)
//    Map<PTRef,bool,PTRefHash> mod_ineqs;        // b > 0 -> 0 <= a % b < b, b < 0 -> b < a % b <= 0
//    Map<PTRef,bool,PTRefHash> inc_diseqs;       // a++ != a (< is not safe for overflows for some compiler semantics)
//    Map<PTRef,bool,PTRefHash> compl_diseqs;     // ~a != a

//  public:
//    void getCommEqs(vec<PTRef>& out) const { comm_eqs.getKeys(out); }

  protected:
    Logic_t logic_type;
    SymRef              sym_BV_ZERO;   // 0
    SymRef              sym_BV_ONE;    // 1
    SymRef              sym_BV_MINUS;  // -
    SymRef              sym_BV_PLUS;   // +
    SymRef              sym_BV_TIMES;  // *
    SymRef              sym_BV_DIV;    // /
    SymRef              sym_BV_EQ;     // ==
    SymRef              sym_BV_SLEQ;    // s<=
    SymRef              sym_BV_ULEQ;    // u<=
    SymRef              sym_BV_LT;     // <
    SymRef              sym_BV_GEQ;    // >=
    SymRef              sym_BV_GT;     // >
    SymRef              sym_BV_LSHIFT; // <<
    SymRef              sym_BV_RSHIFT; // >>
    SymRef              sym_BV_MOD;    // %
    SymRef              sym_BV_BWAND;  // &
    SymRef              sym_BV_BWOR;   // |
    SymRef              sym_BV_INC;    // ++
    SymRef              sym_BV_DEC;    // --
    SymRef              sym_BV_NEQ;    // !=
    SymRef              sym_BV_LAND;   // &&
    SymRef              sym_BV_LOR;    // ||
    SymRef              sym_BV_NEG;    // -
    SymRef              sym_BV_NOT;    // !
    SymRef              sym_BV_COMPL;  // ~
    SymRef              sym_BV_BWXOR;  // ^
    SymRef              sym_BV_COLLATE32; // .coll32

    SRef                sort_BVNUM;

    PTRef               term_BV_ZERO;
    PTRef               term_BV_ONE;

    static int          tk_bv_zero;
    static int          tk_bv_one;
    static const char*  tk_bv_neg;
    static const char*  tk_bv_eq;
    static const char*  tk_bv_minus;
    static const char*  tk_bv_plus;
    static const char*  tk_bv_times;
    static const char*  tk_bv_div;
    static const char*  tk_bv_sleq;
    static const char*  tk_bv_uleq;
    static const char*  tk_bv_lt;
    static const char*  tk_bv_geq;
    static const char*  tk_bv_gt;
    static const char*  tk_bv_lshift;
    static const char*  tk_bv_rshift;
    static const char*  tk_bv_mod;
    static const char*  tk_bv_bwand;
    static const char*  tk_bv_bwor;
    static const char*  tk_bv_land;
    static const char*  tk_bv_lor;
    static const char*  tk_bv_not;
    static const char*  tk_bv_bwxor;
    static const char*  tk_bv_compl;

    static const char*  s_sort_bvnum;
    //static const char*  s_sort_bvstr;

    static const char* tk_bv_coll32;
    static const char* s_uf_extract_base;

    static const int i_default_bitwidth;

    int bitwidth;

  public:
    BVLogic (SMTConfig& c, int width = i_default_bitwidth);
    ~BVLogic();
    virtual int          getBitWidth() const { return bitwidth; }
    virtual const char*   getName()  const { return getLogic().str; }
    virtual const Logic_t getLogic() const { return opensmt::QF_BV; }

//    virtual PTRef         insertTerm(SymRef sym, vec<PTRef>& terms, char** msg);
    virtual PTRef mkConst(const int c) { assert(false); return PTRef_Undef; } // Not allowed (ambiguous)
    PTRef         mkBVConst   (const int c) { assert(c >= 0); char* num; opensmt::uwordToBinary(c, num, getBitWidth()); PTRef tr = Logic::mkConst(sort_BVNUM, num); free(num); return tr; } // Should be converting the int c to binary...
    virtual PTRef         mkNumVar  (const char* name) { assert(false); return PTRef_Undef; } // Not allowed (ambiguous)
    virtual PTRef         mkBVNumVar  (const char* name) { return mkVar(sort_BVNUM, name); }
    virtual bool          isBuiltinSort(SRef sr) const { return (sr == sort_BVNUM) /*|| (sr == sort_BVSTR)*/ || Logic::isBuiltinSort(sr); }
    virtual bool          isBuiltinConstant(SymRef sr) const { return isBVNUMConst(sr) || Logic::isBuiltinConstant(sr); }

    virtual void conjoinExtras(PTRef root, PTRef& root_out) { root_out = root; }

    bool isBVNUMConst(SymRef sr) const { return isConstant(sr) && hasSortBVNUM(sr); }
    bool isBVNUMConst(PTRef tr)  const { return isBVNUMConst(getPterm(tr).symb()); }
    bool hasSortBVNUM(const SymRef sr) const { return getSortRef(sr) == sort_BVNUM; }
    bool hasSortBVNUM(const PTRef tr)  const { return hasSortBVNUM(getPterm(tr).symb()); }

    SRef declareSort_BVNUM(char** msg);
    SRef getSort_BVNUM() const { return sort_BVNUM; }
    const int getBVNUMConst(PTRef tr) const;


    bool isBVPlus(SymRef sr)   const { return sr == sym_BV_PLUS; }
    bool isBVPlus(PTRef tr)    const { return isBVPlus(getPterm(tr).symb()); }
    bool isBVMinus(SymRef sr)  const { return sr == sym_BV_MINUS; }
    bool isBVMinus(PTRef tr)   const { return isBVMinus(getPterm(tr).symb()); }
    bool isBVNeg(SymRef sr)    const { return sr == sym_BV_NEG; }
    bool isBVNeg(PTRef tr)     const { return isBVNeg(getPterm(tr).symb()); }
    bool isBVTimes(SymRef sr)  const { return sr == sym_BV_TIMES; }
    bool isBVTimes(PTRef tr)   const { return isBVTimes(getPterm(tr).symb()); }
    bool isBVDiv(SymRef sr)    const { return sr == sym_BV_DIV; }
    bool isBVDiv(PTRef tr)     const { return isBVDiv(getPterm(tr).symb()); }
    bool isBVEq(SymRef sr)     const { return isEquality(sr) && (sym_store[sr][0] == sort_BVNUM); }
    bool isBVEq(PTRef tr)      const { return isBVEq(getPterm(tr).symb()); }
    bool isBVSleq(SymRef sr)   const { return sr == sym_BV_SLEQ; }
    bool isBVSleq(PTRef tr)    const { return isBVSleq(getPterm(tr).symb()); }
    bool isBVUleq(SymRef sr)   const { return sr == sym_BV_ULEQ; }
    bool isBVUleq(PTRef tr)    const { return isBVUleq(getPterm(tr).symb()); }
    bool isBVLt(SymRef sr)     const { return sr == sym_BV_LT; }
    bool isBVLt(PTRef tr)      const { return isBVLt(getPterm(tr).symb()); }
    bool isBVGeq(SymRef sr)    const { return sr == sym_BV_GEQ; }
    bool isBVGeq(PTRef tr)     const { return isBVGeq(getPterm(tr).symb()); }
    bool isBVGt(SymRef sr)     const { return sr == sym_BV_GT; }
    bool isBVGt(PTRef tr)      const { return isBVGt(getPterm(tr).symb()); }
    bool isBVVar(SymRef sr)    const { return isVar(sr) && sym_store[sr].rsort() == sort_BVNUM; }
    bool isBVVar(PTRef tr)     const { return isBVVar(getPterm(tr).symb()); }
    bool isBVZero(SymRef sr)   const { return sr == sym_BV_ZERO; }
    bool isBVZero(PTRef tr)    const { return tr == term_BV_ZERO; }
    bool isBVOne(SymRef sr)    const { return sr == sym_BV_ONE; }
    bool isBVOne(PTRef tr)     const { return tr == term_BV_ONE; }
    bool isBVLshift(SymRef sr) const { return sr == sym_BV_LSHIFT; }
    bool isBVLshift(PTRef tr)  const { return isBVLshift(getPterm(tr).symb()); }
    bool isBVRshift(SymRef sr) const { return sr == sym_BV_RSHIFT; }
    bool isBVRshift(PTRef tr)  const { return isBVRshift(getPterm(tr).symb()); }
    bool isBVMod(SymRef sr)    const { return sr == sym_BV_MOD; }
    bool isBVMod(PTRef tr)     const { return isBVMod(getPterm(tr).symb()); }
    bool isBVBwAnd(SymRef sr)  const { return sr == sym_BV_BWAND; }
    bool isBVBwAnd(PTRef tr)   const { return isBVBwAnd(getPterm(tr).symb()); }
    bool isBVBwOr(SymRef sr)   const { return sr == sym_BV_BWOR; }
    bool isBVBwOr(PTRef tr)    const { return isBVBwOr(getPterm(tr).symb()); }
    bool isBVInc(SymRef sr)    const { return sr == sym_BV_INC; }
    bool isBVInc(PTRef tr)     const { return isBVInc(getPterm(tr).symb()); }
    bool isBVDec(SymRef sr)    const { return sr == sym_BV_DEC; }
    bool isBVDec(PTRef tr)     const { return isBVDec(getPterm(tr).symb()); }
    bool isBVNeq(SymRef sr)    const { return sr == sym_BV_NEQ; }
    bool isBVNeq(PTRef tr)     const { return isBVNeq(getPterm(tr).symb()); }
    bool isBVLand(SymRef sr)   const { return sr == sym_BV_LAND; }
    bool isBVLand(PTRef tr)    const { return isBVLand(getPterm(tr).symb()); }
    bool isBVLor(SymRef sr)    const { return sr == sym_BV_LOR; }
    bool isBVLor(PTRef tr)     const { return isBVLor(getPterm(tr).symb()); }
    bool isBVNot(SymRef sr)    const { return sr == sym_BV_NOT; }
    bool isBVNot(PTRef tr)     const { return isBVNot(getPterm(tr).symb()); }
    bool isBVBwXor(SymRef sr)  const { return sr == sym_BV_BWXOR; }
    bool isBVBwXor(PTRef tr)   const { return isBVBwXor(getPterm(tr).symb()); }
    bool isBVCompl(SymRef sr)  const { return sr == sym_BV_COMPL; }
    bool isBVCompl(PTRef tr)   const { return isBVCompl(getPterm(tr).symb()); }

    bool isUFEquality(PTRef tr) const { return !isBVEq(tr) && Logic::isUFEquality(tr); }
    bool isTheoryEquality(PTRef tr) const { return isBVEq(tr); }
    bool isUF(PTRef tr) const { return !hasSortBVNUM(tr) && Logic::isUF(tr); }

    PTRef getTerm_BVZero() { return term_BV_ZERO; }
    PTRef getTerm_BVOne()  { return term_BV_ONE; }

    PTRef mkBVNeg(const vec<PTRef>& args) { assert(args.size() == 1); return mkBVNeg(args[0]); }
    PTRef mkBVNeg(PTRef, char**);
    PTRef mkBVNeg(PTRef tr) {char* msg; PTRef trn = mkBVNeg(tr, &msg); assert(trn != PTRef_Undef); return trn; }

    PTRef mkBVMinus(const vec<PTRef>&, char**);
    PTRef mkBVMinus(const vec<PTRef>& args) { char *msg; PTRef tr = mkBVMinus(args, &msg); assert(tr != PTRef_Undef); return tr; }
    PTRef mkBVMinus(const PTRef a1, const PTRef a2) { vec<PTRef> tmp; tmp.push(a1); tmp.push(a2); return mkBVMinus(tmp); }

    PTRef mkBVPlus(const vec<PTRef>& args) { assert(args.size() == 2); return mkBVPlus(args[0], args[1]); }
    PTRef mkBVPlus(const PTRef arg1, const PTRef arg2, char**);
    PTRef mkBVPlus(const PTRef arg1, const PTRef arg2) { char *msg; PTRef tr = mkBVPlus(arg1, arg2, &msg); assert(tr != PTRef_Undef); return tr; }

    PTRef mkBVTimes(const vec<PTRef>& args) {assert(args.size() == 2); return mkBVTimes(args[0], args[1]);}
    PTRef mkBVTimes(const PTRef, const PTRef, char**);
    PTRef mkBVTimes(const PTRef arg1, const PTRef arg2) { char *msg; PTRef tr = mkBVTimes(arg1, arg2, &msg); assert(tr != PTRef_Undef); return tr; }

    PTRef mkBVDiv(const vec<PTRef>& args) {assert(args.size() == 2); return mkBVDiv(args[0], args[1]);}
    PTRef mkBVDiv(const PTRef nom, const PTRef den);

    PTRef mkBVSleq(const PTRef arg1, const PTRef arg2, char**);
    PTRef mkBVSleq(const vec<PTRef>& args) {assert(args.size() == 2); char *msg; return mkBVSleq(args[0], args[1], &msg);}

    PTRef mkBVUleq(const PTRef arg1, const PTRef arg2, char**);
    PTRef mkBVUleq(const vec<PTRef>& args) {assert(args.size() == 2); char *msg; return mkBVUleq(args[0], args[1], &msg);}

    PTRef mkBVGeq(const vec<PTRef>& args) {assert(args.size() == 2); char *msg; return mkBVGeq(args[0], args[1], &msg);}
    PTRef mkBVGeq(const PTRef arg1, const PTRef arg2, char**);

    PTRef mkBVLt(const vec<PTRef>& args) {assert(args.size() == 2); char *msg; return mkBVLt(args[0], args[1], &msg);}
    PTRef mkBVLt(const PTRef arg1, const PTRef arg2, char** tmp);

    PTRef mkBVGt(const vec<PTRef>& args) {assert(args.size() == 2); char *msg; return mkBVGt(args[0], args[1], &msg);}
    PTRef mkBVGt(const PTRef arg1, const PTRef arg2, char** tmp);

    PTRef mkBVLshift(const vec<PTRef>& args) {assert(args.size() == 2); return mkBVLshift(args[0], args[1]);}
    PTRef mkBVLshift   (const PTRef, const PTRef);

    PTRef mkBVRshift(const vec<PTRef>& args) {assert(args.size() == 2); return mkBVRshift(args[0], args[1]);}
    PTRef mkBVRshift   (const PTRef, const PTRef);

    PTRef mkBVMod(const vec<PTRef>& args) {assert(args.size() == 2); return mkBVMod(args[0], args[1]);}
    PTRef mkBVMod      (const PTRef, const PTRef);

    PTRef mkBVBwAnd(const vec<PTRef>& args) {assert(args.size() == 2); return mkBVBwAnd(args[0], args[1]);}
    PTRef mkBVBwAnd    (const PTRef, const PTRef);

    PTRef mkBVBwOr(const vec<PTRef>& args) {assert(args.size() == 2); return mkBVBwOr(args[0], args[1]);}
    PTRef mkBVBwOr     (const PTRef, const PTRef);

    /*PTRef mkBVInc(const vec<PTRef>& args) {assert(args.size() == 1);  return mkBVInc(args[0]);}
    PTRef mkBVInc      (const PTRef);

    PTRef mkBVDec(const vec<PTRef>& args) {assert(args.size() == 1);  return mkBVDec(args[0]);}
    PTRef mkBVDec      (const PTRef);*/

    PTRef mkBVEq(const vec<PTRef>& args) {assert(args.size() == 2); return mkBVEq(args[0], args[1]);}
    PTRef mkBVEq      (const PTRef, const PTRef);

    PTRef mkBVNeq(const vec<PTRef>& args) {assert(args.size() == 2); return mkBVNeq(args[0], args[1]);}
    PTRef mkBVNeq      (const PTRef, const PTRef);

    PTRef mkBVLand(const vec<PTRef>& args) {assert(args.size() == 2); return mkBVLand(args[0], args[1]);}
    PTRef mkBVLand     (const PTRef, const PTRef);

    PTRef mkBVLor(const vec<PTRef>& args) {assert(args.size() == 2); return mkBVLor(args[0], args[1]);}
    PTRef mkBVLor      (const PTRef, const PTRef);

    PTRef mkBVNot(const vec<PTRef>& args) {assert(args.size() == 1); return mkBVNot(args[0]);}
    PTRef mkBVNot      (const PTRef);

    PTRef mkBVBwXor(const vec<PTRef>& args) {assert(args.size() == 2); return mkBVBwXor(args[0], args[1]);}
    PTRef mkBVBwXor    (const PTRef, const PTRef);

    PTRef mkBVCompl(const vec<PTRef>& args) {assert(args.size() == 1); return mkBVCompl(args[0]);}
    PTRef mkBVCompl    (const PTRef);

    PTRef mkGlueBtoUF(const vec<PTRef>& bits, PTRef tr);
    PTRef mkGlueUFtoB(PTRef tr, const vec<PTRef>& bits);

    PTRef mkCollate32(const vec<PTRef>& bits);
    PTRef mkExtract(PTRef tr, int i);

/*  PTRef mkBVSizeof(const vec<PTRef>& args) {assert(args.size() == 1); return mkBVSizeof(args[0]);}
    PTRef mkBVSizeof   (const PTRef);

    PTRef mkBVAddrof(const vec<PTRef>& args) {assert(args.size() == 1); return mkBVAddrof(args[0]);}
    PTRef mkBVAddrof   (const PTRef);

    PTRef mkBVPtr(const vec<PTRef>& args) {assert(args.size() == 1); return mkBVPtr(args[0]);}
    PTRef mkBVPtr      (const PTRef);

    PTRef mkBVCond(const vec<PTRef>& args) {assert(args.size() == 3); return mkBVCond(args[0], args[1], args[2]);}
    PTRef mkBVCond     (const PTRef, const PTRef, const PTRef);*/

};
#endif




