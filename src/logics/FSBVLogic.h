/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */


#ifndef OPENSMT_FSBVLOGIC_H
#define OPENSMT_FSBVLOGIC_H
#include "Logic.h"
#include "NumberUtils.h"

using BitWidth_t = uint32_t;

class FSBVLogic : public Logic {
    struct BitWidth_t_Hash{
        uint32_t operator () (BitWidth_t bw) const {
            return (uint32_t)bw; }
    };
    Map<BitWidth_t, SRef, BitWidth_t_Hash> bitWidthToBitWidthSort;
    Map<BitWidth_t, SRef, BitWidth_t_Hash> bitWidthToBitVectorSort;
    Map<SRef, bool, SRefHash> bitVectorSorts;
    Map<SRef, BitWidth_t, SRefHash> bitWidthSortToBitWidth;

    static constexpr const char *BVHexPrefix = "#x";
    static constexpr const char *BVBinPrefix = "#b";

    static constexpr const char *tk_bvconcat = "concat";
    static constexpr const char *tk_bvbasesort = "BitVec";
    static constexpr const char *tk_bvnot = "bvnot";
    static constexpr const char *tk_bvneg = "bvneg";
    static constexpr const char *tk_bvand = "bvand";
    static constexpr const char *tk_bvor = "bvor";
    static constexpr const char *tk_bvadd = "bvadd";
    static constexpr const char *tk_bvmul = "bvmul";
    static constexpr const char *tk_bvudiv = "bvudiv";
    static constexpr const char *tk_bvurem = "bvurem";
    static constexpr const char *tk_bvshl = "bvshl";
    static constexpr const char *tk_bvlshr = "bvlshr";
    static constexpr const char *tk_bvult ="bvult";

    static constexpr const char *tk_extract = "extract";
    static constexpr const char *tk_div = "div";
    static constexpr const char *tk_rem = "rem";

    SSymRef             sym_BVBaseSort;
    SRef                BVBaseSort;

//    Map<SRef, SymRef, SRefHash> concatenation_syms;
    Map<SRef, SymRef, SRefHash> not_syms;
    Map<SRef, SymRef, SRefHash> neg_syms;
    Map<SRef, SymRef, SRefHash> and_syms;
    Map<SRef, SymRef, SRefHash> or_syms;
    Map<SRef, SymRef, SRefHash> add_syms;
    Map<SRef, SymRef, SRefHash> mul_syms;
    Map<SRef, SymRef, SRefHash> udiv_syms;
    Map<SRef, SymRef, SRefHash> urem_syms;
    Map<SRef, SymRef, SRefHash> shl_syms;
    Map<SRef, SymRef, SRefHash> lshr_syms;
    Map<SRef, SymRef, SRefHash> ult_syms;

    SRef makeBitWidthSortForBW(BitWidth_t m);

    bool isBitVectorSort(SRef sr) const { return sort_store[sr].getSymRef() == sym_IndexedSort and sort_store[sr].getSize() == 2 and sort_store[sort_store[sr][0]].getSymRef() == sym_BVBaseSort; }

    SymRef mkBVConcatSym(SRef lhs, SRef rhs);
    SymRef mkBVNegSym(SRef a);
    SymRef mkBVNotSym(SRef a);
    SymRef mkBVAndSym(SRef a);
    SymRef mkBVOrSym(SRef a);
    SymRef mkBVAddSym(SRef a);
    SymRef mkBVMulSym(SRef a);
    SymRef mkBVUdivSym(SRef a);
    SymRef mkBVUremSym(SRef a);
    SymRef mkBVShlSym(SRef a);
    SymRef mkBVLshrSym(SRef a);
    SymRef mkBVUltSym(SRef a);

public:
    FSBVLogic(opensmt::Logic_t type);


    virtual bool isBuiltinSort(SRef sr) const override { return (sort_store[sr].getSymRef() == sym_IndexedSort and sort_store[sr][0] == BVBaseSort) or Logic::isBuiltinSort(sr); }
    virtual bool isBuiltinConstant(SymRef sr) const override { return isBVConst(sr) || Logic::isBuiltinConstant(sr); }

    SRef makeBitVectorSortForBW(BitWidth_t m);
    BitWidth_t getBitWidth(SRef sr) const { assert(isBitVectorSort(sr)); return std::stoi(sort_store.getSortSymName(sort_store[sr][1])); }
    BitWidth_t getRetSortBitWidth(PTRef tr) const { SRef sr = getSortRef(tr); assert(isBitVectorSort(sr)); return getBitWidth(sr); }

    bool yieldsSortBV(SymRef sr) const { return bitVectorSorts.has(getSortRef(sr)); }
    bool yieldsSortBV(PTRef tr) const { return yieldsSortBV(getSymRef(tr)); }

    PTRef mkBVConstFromHex(std::string const & hexString);
    PTRef mkBVConstFromBin(std::string const & binString);
    PTRef mkBVConst(BitWidth_t m, unsigned c);
    PTRef mkBVConst(SymRef sym);
    PTRef mkBVVar(BitWidth_t m, std::string const & name) { return mkVar(makeBitVectorSortForBW(m), name.c_str()); }

    PTRef mkBVConcat(PTRef lhs, PTRef rhs);

    PTRef mkBVNeg(PTRef a);
    PTRef mkBVNot(PTRef a);

    PTRef mkBVAnd(vec<PTRef> const & args);
    PTRef mkBVAnd(PTRef a1, PTRef a2);

    PTRef mkBVOr(PTRef a1, PTRef a2);
    PTRef mkBVOr(vec<PTRef> const & args);

    PTRef mkBVAdd(vec<PTRef> const & args);
    PTRef mkBVAdd(PTRef a1, PTRef a2);

    PTRef mkBVMul(vec<PTRef> const & args);
    PTRef mkBVMul(PTRef a1, PTRef a2);
    PTRef mkBVUdiv(PTRef dividend, PTRef divisor);
    PTRef mkBVUrem(PTRef dividend, PTRef divisor);
    PTRef mkBVShl(PTRef a, PTRef shift);
    PTRef mkBVLshr(PTRef a, PTRef shift);
    PTRef mkBVUlt(PTRef lhs, PTRef rhs);

    bool isBVConst(SymRef sr) const { return isConstant(sr) and yieldsSortBV(sr); }
    bool isBVVar(SymRef sr) const { return isVar(sr) and yieldsSortBV(sr); }

    bool isEqualAsString(char const * x, char const * y) const { return std::string(x) == y; }
    bool isBVConcat(SymRef sr) const { return isEqualAsString(tk_bvconcat, getSymName(sr)); }
    bool isBVNeg(SymRef sr) const { return isEqualAsString(tk_bvneg, getSymName(sr)); }
    bool isBVNot(SymRef sr) const { return isEqualAsString(tk_bvnot, getSymName(sr)); }
    bool isBVAnd(SymRef sr) const { return isEqualAsString(tk_bvand, getSymName(sr)); }
    bool isBVOr(SymRef sr) const { return isEqualAsString(tk_bvor, getSymName(sr)); }
    bool isBVAdd(SymRef sr) const { return isEqualAsString(tk_bvadd, getSymName(sr)); }
    bool isBVMul(SymRef sr) const { return isEqualAsString(tk_bvmul, getSymName(sr)); }
    bool isBVUdiv(SymRef sr) const { return isEqualAsString(tk_bvudiv, getSymName(sr)); }
    bool isBVUrem(SymRef sr) const { return isEqualAsString(tk_bvurem, getSymName(sr)); }
    bool isBVShl(SymRef sr) const { return isEqualAsString(tk_bvshl, getSymName(sr)); }
    bool isBVLshr(SymRef sr) const { return isEqualAsString(tk_bvlshr, getSymName(sr)); }
    bool isBVUlt(SymRef sr) const { return isEqualAsString(tk_bvult, getSymName(sr)); }

    PTRef resolveTerm(char const * s, vec<PTRef> && args, SRef, SymbolMatcher) override;
    PTRef insertTerm (SymRef sym, vec<PTRef> && args) override;
    std::string printSym(SymRef sr) const override { return isBVConst(sr) ? getSymName(sr) : Logic::printSym(sr); }
};

#endif //OPENSMT_FSBVLOGIC_H
