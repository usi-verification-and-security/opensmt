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

class FSBVLogic : public Logic {
    using BitWidth_t = uint32_t;
    struct BitWidth_t_Hash{
        uint32_t operator () (BitWidth_t bw) const {
            return (uint32_t)bw; }
    };
    Map<BitWidth_t, SRef, BitWidth_t_Hash> bitWidthToBitWidthSort;
    Map<BitWidth_t, SRef, BitWidth_t_Hash> bitWidthToBitVectorSort;
    Map<SRef, bool, SRefHash> bitVectorSorts;
    Map<SRef, BitWidth_t, SRefHash> bitWidthSortToBitWidth;
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
public:
    FSBVLogic(opensmt::Logic_t type);

    PTRef mkBVConstFromHex(std::string const & hexString);
    PTRef mkBVConstFromBin(std::string const & binString);
    PTRef mkBVConst(BitWidth_t m, unsigned c);
    PTRef mkBVVar(BitWidth_t m, std::string const & name) { return mkVar(makeBitVectorSortForBW(m), name.c_str()); }

    virtual bool isBuiltinSort(SRef sr) const override { return (sort_store[sr].getSymRef() == sym_IndexedSort and sort_store[sr][0] == BVBaseSort) or Logic::isBuiltinSort(sr); }
    virtual bool isBuiltinConstant(SymRef sr) const override { return isBVConst(sr) || Logic::isBuiltinConstant(sr); }

    SRef makeBitVectorSortForBW(BitWidth_t m);
    SRef getBitVectorSortForBW(BitWidth_t m) const;
    bool hasSortBitVector(SymRef sr);
    bool isBVConst(SymRef sr) const { return isConstant(sr) && yieldsSortBV(sr); }
    bool isBVConst(PTRef tr) const { return isBVConst(getSymRef(tr)); }
    bool yieldsSortBV(SymRef sr) const { return bitVectorSorts.has(getSortRef(sr)); }
    bool yieldsSortBV(PTRef tr) const { return yieldsSortBV(getSymRef(tr)); }

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
    PTRef mkBVSHL(PTRef a, PTRef shift);
    PTRef mkBVLSHR(PTRef a, PTRef shift);
    PTRef mkBVULT(PTRef lhs, PTRef rhs);
};

#endif //OPENSMT_FSBVLOGIC_H
