/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "FSBVLogic.h"

FSBVLogic::FSBVLogic(opensmt::Logic_t type)
    : Logic(type)
    , sym_BVBaseSort(sort_store.newSortSymbol(SortSymbol(tk_bvbasesort, 0, SortSymbol::INTERNAL)))
    , BVBaseSort(sort_store.getOrCreateSort(sym_BVBaseSort, {}).first)
{ }

SRef FSBVLogic::makeBitWidthSortForBW(BitWidth_t m) {
    SRef bwSort;
    if (bitWidthToBitWidthSort.peek(m, bwSort)) {
        return bwSort;
    }
    std::string const bw_string = std::to_string(m);
    SSymRef bwSortSym = sort_store.newSortSymbol(SortSymbol(bw_string, 0, SortSymbol::INTERNAL));
    // Do not create core predicates for bit width sorts
    bwSort = sort_store.getOrCreateSort(bwSortSym, {}).first;
    assert(not bitWidthToBitWidthSort.has(m));
    bitWidthToBitWidthSort.insert(m, bwSort);
    bitWidthSortToBitWidth.insert(bwSort, m);
    return bwSort;
}

SRef FSBVLogic::makeBitVectorSortForBW(BitWidth_t m) {
    SRef bvSort;
    if (bitWidthToBitVectorSort.peek(m, bvSort)) {
        return bvSort;
    }
    SRef bwSort = makeBitWidthSortForBW(m);

    // Create core predicates for bit vector sorts
    bvSort = getSort(sym_IndexedSort, {BVBaseSort, bwSort});

    bitWidthToBitVectorSort.insert(m, bvSort);
    bitVectorSorts.insert(bvSort, true);
    return bvSort;
}

SRef FSBVLogic::getBitVectorSortForBW(BitWidth_t m) const {
    SRef bwSort;
    if (bitWidthToBitVectorSort.peek(m, bwSort)) {
        return bwSort;
    } else {
        return SRef_Undef;
    }
}

PTRef FSBVLogic::mkBVConst(BitWidth_t m, unsigned c) {
    char * num;
    opensmt::wordToBinary(c, num, m);
    PTRef tr = mkConst(makeBitVectorSortForBW(m), num);
    return tr;
}

PTRef FSBVLogic::mkBVAdd(PTRef a1, PTRef a2) {
    if (not bitVectorSorts.has(getSortRef(a1))) {
        throw OsmtApiException("mkBVAdd called for non-bitvector sort " + printSort(getSortRef(a1)));
    }
    SRef sr = getSortRef(a1);
    SymRef addSym;
    if (not add_syms.peek(sr, addSym)) {
        addSym = declareFun_NoScoping_LeftAssoc(tk_bvadd, sr, {sr, sr});
    }
    std::string why;
    if (not typeCheck(addSym, {a1, a2}, why)) {
        throw OsmtApiException(why);
    }
    return mkFun(addSym, {a1, a2});
}

PTRef FSBVLogic::mkBVConcat(PTRef lhs, PTRef rhs) {
    SRef lhsSort = getSortRef(lhs);
    SRef rhsSort = getSortRef(rhs);
    if (not bitVectorSorts.has(lhsSort) or not bitVectorSorts.has(rhsSort)) {
        throw OsmtApiException("mkBVConcat called for incompatible sorts " + printSort(lhsSort) \
        + " and " + printSort(rhsSort));
    }
    SRef lhsBWSort  = sort_store[lhsSort][1];
    SRef rhsBWSort = sort_store[rhsSort][1];
    BitWidth_t lhsbw = bitWidthSortToBitWidth[lhsBWSort];
    BitWidth_t rhsbw = bitWidthSortToBitWidth[rhsBWSort];
    BitWidth_t returnBitWidth = lhsbw + rhsbw;

    SRef returnBitVectorSort = makeBitVectorSortForBW(returnBitWidth);
    SymRef BVConcatSym = declareFun_NoScoping(tk_bvconcat, returnBitVectorSort, {lhsSort, rhsSort});
    return mkFun(BVConcatSym, {lhs, rhs});
}

PTRef FSBVLogic::mkBVNeg(PTRef a) {
    SRef sr = getSortRef(a);
    if (not bitVectorSorts.has(sr)) {
        throw OsmtApiException("mkBVNeg called for unrelated sort " + printSort(sr));
    }

    SymRef BVNeg = declareFun_NoScoping(tk_bvneg, sr, {sr});
    return mkFun(BVNeg, {a});

}

PTRef FSBVLogic::mkBVNot(PTRef a) {
    SRef sr = getSortRef(a);
    if (not bitVectorSorts.has(sr)) {
        throw OsmtApiException("mkBVNoot called for unrelated sort " + printSort(sr));
    }

    SymRef BVNot = declareFun_NoScoping(tk_bvnot, sr, {sr});

    return mkFun(BVNot, {a});
}

PTRef FSBVLogic::mkBVAnd(PTRef a1, PTRef a2) {
    SRef sr = getSortRef(a1);
    if (not bitVectorSorts.has(sr)) {
        throw OsmtApiException("mkBVAnd called for unrelated sort " + printSort(sr));
    }

    SymRef BVAnd = declareFun_NoScoping_LeftAssoc(tk_bvand, sr, {sr, sr});
    std::string why;
    if (not typeCheck(BVAnd, {a1, a2}, why)) {
        throw OsmtApiException(why);
    }

    return mkFun(BVAnd, {a1, a2});
}

PTRef FSBVLogic::mkBVOr(PTRef a1, PTRef a2) {
    SRef sr = getSortRef(a1);
    if (not bitVectorSorts.has(sr)) {
        throw OsmtApiException("mkBVOr called for unrelated sort " + printSort(sr));
    }

    SymRef BVOr = declareFun_NoScoping_LeftAssoc(tk_bvor, sr, {sr, sr});
    std::string why;
    if (not typeCheck(BVOr, {a1, a2}, why)) {
        throw OsmtApiException(why);
    }

    return mkFun(BVOr, {a1, a2});
}

PTRef FSBVLogic::mkBVMul(PTRef a1, PTRef a2) {
    SRef sr = getSortRef(a1);
    if (not bitVectorSorts.has(sr)) {
        throw OsmtApiException("mkBVMul called for unrelated sort " + printSort(sr));
    }

    SymRef BVMul = declareFun_NoScoping_LeftAssoc(tk_bvmul, sr, {sr, sr});
    std::string why;
    if (not typeCheck(BVMul, {a1, a2}, why)) {
        throw OsmtApiException(why);
    }

    return mkFun(BVMul, {a1, a2});
}

PTRef FSBVLogic::mkBVUdiv(PTRef a1, PTRef a2) {
    SRef sr = getSortRef(a1);
    if (not bitVectorSorts.has(sr)) {
        throw OsmtApiException("mkBVUdiv called for unrelated sort " + printSort(sr));
    }

    SymRef BVUdiv = declareFun_NoScoping_LeftAssoc(tk_bvudiv, sr, {sr, sr});
    std::string why;
    if (not typeCheck(BVUdiv, {a1, a2}, why)) {
        throw OsmtApiException(why);
    }

    return mkFun(BVUdiv, {a1, a2});
}

PTRef FSBVLogic::mkBVUrem(PTRef a1, PTRef a2) {
    SRef sr = getSortRef(a1);
    if (not bitVectorSorts.has(sr)) {
        throw OsmtApiException("mkBVUrem called for unrelated sort " + printSort(sr));
    }

    SymRef BVUrem = declareFun_NoScoping_LeftAssoc(tk_bvurem, sr, {sr, sr});
    std::string why;
    if (not typeCheck(BVUrem, {a1, a2}, why)) {
        throw OsmtApiException(why);
    }

    return mkFun(BVUrem, {a1, a2});
}

PTRef FSBVLogic::mkBVSHL(PTRef a, PTRef shift) {
    SRef sr = getSortRef(a);
    if (not bitVectorSorts.has(sr)) {
        throw OsmtApiException("mkBVSHL called for unrelated sort " + printSort(sr));
    }

    SymRef BVSHL = declareFun_NoScoping_LeftAssoc(tk_bvshl, sr, {sr, sr});
    std::string why;
    if (not typeCheck(BVSHL, {a, shift}, why)) {
        throw OsmtApiException(why);
    }

    return mkFun(BVSHL, {a, shift});
}

PTRef FSBVLogic::mkBVLSHR(PTRef a, PTRef shift) {
    SRef sr = getSortRef(a);
    if (not bitVectorSorts.has(sr)) {
        throw OsmtApiException("mkBVLSHR called for unrelated sort " + printSort(sr));
    }

    SymRef BVLSHR = declareFun_NoScoping_LeftAssoc(tk_bvlshr, sr, {sr, sr});
    std::string why;
    if (not typeCheck(BVLSHR, {a, shift}, why)) {
        throw OsmtApiException(why);
    }

    return mkFun(BVLSHR, {a, shift});
}

PTRef FSBVLogic::mkBVULT(PTRef lhs, PTRef rhs) {
    SRef sr = getSortRef(lhs);
    if (not bitVectorSorts.has(sr)) {
        throw OsmtApiException("mkBVULT called for unrelated sort " + printSort(sr));
    }

    SymRef BVULT = declareFun_NoScoping_LeftAssoc(tk_bvult, sr, {sr, sr});
    std::string why;
    if (not typeCheck(BVULT, {lhs, rhs}, why)) {
        throw OsmtApiException(why);
    }

    return mkFun(BVULT, {lhs, rhs});
}
