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

    std::string const bw_string = std::to_string(m);
    SSymRef bwSortSym;
    SortSymbol bw_sortSymbol(bw_string, 0, SortSymbol::INTERNAL);
    if (not sort_store.peek(bw_sortSymbol, bwSortSym)) {
        bwSortSym = sort_store.newSortSymbol(SortSymbol(bw_string, 0, SortSymbol::INTERNAL));
    }
    // Do not create core predicates for bit width sorts
    SRef bwSort = sort_store.getOrCreateSort(bwSortSym, {}).first;

    return bwSort;
}

SRef FSBVLogic::makeBitVectorSortForBW(BitWidth_t m) {
    SRef bwSort = makeBitWidthSortForBW(m);
    // Create core predicates for bit vector sorts
    SRef bvSort = getSort(sym_IndexedSort, {BVBaseSort, bwSort});
    return bvSort;
}

PTRef FSBVLogic::mkBVConstFromHex(std::string const & hex) {
    return mkConst(makeBitVectorSortForBW((hex.length()-2)*4), hex.c_str()); // TODO: convert hex to binary
}

PTRef FSBVLogic::mkBVConstFromBin(std::string const & bin) {
    return mkConst(makeBitVectorSortForBW(bin.length()-2), bin.c_str());
}

PTRef FSBVLogic::mkBVConst(BitWidth_t m, unsigned c) {
    std::string bitString = "#b" + opensmt::wordToBinary(c, m);
    return mkConst(makeBitVectorSortForBW(m), bitString.c_str());
}

PTRef FSBVLogic::mkBVConst(SymRef sym) {
    return mkConst(getSortRef(sym), sym_store.getName(sym));
}

SymRef FSBVLogic::mkBVAddSym(SRef a) {

    if (not isBitVectorSort(a)) {
        throw OsmtApiException("mkBVAdd called for non-bitvector sort " + printSort(a));
    }
    SymRef addSym;
    if (not add_syms.peek(a, addSym)) {
        addSym = declareFun_NoScoping_LeftAssoc(tk_bvadd, a, {a, a});
    }
    return addSym;
}

PTRef FSBVLogic::mkBVAdd(PTRef a1, PTRef a2) {
    SymRef addSym = mkBVAddSym(getSortRef(a1));
    std::string why;
    if (not typeCheck(addSym, {a1, a2}, why)) {
        throw OsmtApiException(why);
    }
    return mkFun(addSym, {a1, a2});
}

PTRef FSBVLogic::mkBVAdd(vec<PTRef> const & args) {
    if (args.size() < 2) {
        throw OsmtApiException(std::string(tk_bvadd) + " requires at least two arguments");
    }
    PTRef tr = mkBVAdd(args[0], args[1]);
    for (int i = 2; i < args.size(); i++) {
        tr = mkBVAdd(tr, args[i]);
    }
    return tr;
}

SymRef FSBVLogic::mkBVConcatSym(SRef lhsSort, SRef rhsSort) {
    if (not isBitVectorSort(lhsSort) or not isBitVectorSort(rhsSort)) {
        throw OsmtApiException("mkBVConcat called for incompatible sorts " + printSort(lhsSort) \
        + " and " + printSort(rhsSort));
    }
    BitWidth_t lhsbw = getBitWidth(lhsSort);
    BitWidth_t rhsbw = getBitWidth(rhsSort);
    BitWidth_t returnBitWidth = lhsbw + rhsbw;

    SRef returnBitVectorSort = makeBitVectorSortForBW(returnBitWidth);
    return declareFun_NoScoping(tk_bvconcat, returnBitVectorSort, {lhsSort, rhsSort});
}

PTRef FSBVLogic::mkBVConcat(PTRef lhs, PTRef rhs) {
    SymRef BVConcatSym = mkBVConcatSym(getSortRef(lhs), getSortRef(rhs));
    return mkFun(BVConcatSym, {lhs, rhs});
}

SymRef FSBVLogic::mkBVNegSym(SRef sr) {
    if (not isBitVectorSort(sr)) {
        throw OsmtApiException("mkBVNeg called for unrelated sort " + printSort(sr));
    }
    return declareFun_NoScoping(tk_bvneg, sr, {sr});
}

PTRef FSBVLogic::mkBVNeg(PTRef a) {
    SymRef BVNeg = mkBVNegSym(getSortRef(a));
    return mkFun(BVNeg, {a});
}

SymRef FSBVLogic::mkBVNotSym(SRef sr) {
    if (not isBitVectorSort(sr)) {
        throw OsmtApiException("mkBVNoot called for unrelated sort " + printSort(sr));
    }
    return declareFun_NoScoping(tk_bvnot, sr, {sr});
}

PTRef FSBVLogic::mkBVNot(PTRef a) {
    SymRef BVNot = mkBVNotSym(getSortRef(a));
    return mkFun(BVNot, {a});
}

SymRef FSBVLogic::mkBVAndSym(SRef sr) {
    if (not isBitVectorSort(sr)) {
        throw OsmtApiException("mkBVAnd called for unrelated sort " + printSort(sr));
    }
    return declareFun_NoScoping_LeftAssoc(tk_bvand, sr, {sr, sr});
}

PTRef FSBVLogic::mkBVAnd(PTRef a1, PTRef a2) {
    SymRef BVAnd = mkBVAndSym(getSortRef(a1));
    std::string why;
    if (not typeCheck(BVAnd, {a1, a2}, why)) {
        throw OsmtApiException(why);
    }
    return mkFun(BVAnd, {a1, a2});
}

PTRef FSBVLogic::mkBVAnd(vec<PTRef> const & args) {
    if (args.size() < 2) {
        throw OsmtApiException(std::string(tk_bvand) + " requires at least two arguments");
    }
    PTRef tr = mkBVAnd(args[0], args[1]);
    for (int i = 2; i < args.size(); i++) {
        tr = mkBVAnd(tr, args[i]);
    }
    return tr;
}

SymRef FSBVLogic::mkBVOrSym(SRef sr) {
    if (not isBitVectorSort(sr)) {
        throw OsmtApiException("mkBVOr called for unrelated sort " + printSort(sr));
    }
    return declareFun_NoScoping_LeftAssoc(tk_bvor, sr, {sr, sr});
}

PTRef FSBVLogic::mkBVOr(PTRef a1, PTRef a2) {
    SymRef BVOr = mkBVOrSym(getSortRef(a1));
    std::string why;
    if (not typeCheck(BVOr, {a1, a2}, why)) {
        throw OsmtApiException(why);
    }
    return mkFun(BVOr, {a1, a2});
}

PTRef FSBVLogic::mkBVOr(vec<PTRef> const & args) {
    if (args.size() < 2) {
        throw OsmtApiException(std::string(tk_bvor) + " requires at least two arguments");
    }
    PTRef tr = mkBVOr(args[0], args[1]);
    for (int i = 2; i < args.size(); i++) {
        tr = mkBVOr(tr, args[i]);
    }
    return tr;
}

SymRef FSBVLogic::mkBVMulSym(SRef sr) {
    if (not isBitVectorSort(sr)) {
        throw OsmtApiException("mkBVMul called for unrelated sort " + printSort(sr));
    }
    return declareFun_NoScoping_LeftAssoc(tk_bvmul, sr, {sr, sr});
}

PTRef FSBVLogic::mkBVMul(PTRef a1, PTRef a2) {
    SymRef BVMul = mkBVMulSym(getSortRef(a1));
    std::string why;
    if (not typeCheck(BVMul, {a1, a2}, why)) {
        throw OsmtApiException(why);
    }

    return mkFun(BVMul, {a1, a2});
}

PTRef FSBVLogic::mkBVMul(vec<PTRef> const & args) {
    if (args.size() < 2) {
        throw OsmtApiException(std::string(tk_bvmul) + " requires at least two arguments");
    }
    PTRef tr = mkBVMul(args[0], args[1]);
    for (int i = 2; i < args.size(); i++) {
        tr = mkBVMul(tr, args[i]);
    }
    return tr;
}

SymRef FSBVLogic::mkBVUdivSym(SRef sr) {
    if (not isBitVectorSort(sr)) {
        throw OsmtApiException("mkBVUdiv called for unrelated sort " + printSort(sr));
    }
    return declareFun_NoScoping_LeftAssoc(tk_bvudiv, sr, {sr, sr});
}

PTRef FSBVLogic::mkBVUdiv(PTRef a1, PTRef a2) {
    SymRef BVUdiv = mkBVUdivSym(getSortRef(a1));
    std::string why;
    if (not typeCheck(BVUdiv, {a1, a2}, why)) {
        throw OsmtApiException(why);
    }
    return mkFun(BVUdiv, {a1, a2});
}

SymRef FSBVLogic::mkBVUremSym(SRef sr) {
    if (not isBitVectorSort(sr)) {
        throw OsmtApiException("mkBVUrem called for unrelated sort " + printSort(sr));
    }
    return declareFun_NoScoping_LeftAssoc(tk_bvurem, sr, {sr, sr});
}

PTRef FSBVLogic::mkBVUrem(PTRef a1, PTRef a2) {
    SymRef BVUrem = mkBVUremSym(getSortRef(a1));
    std::string why;
    if (not typeCheck(BVUrem, {a1, a2}, why)) {
        throw OsmtApiException(why);
    }
    return mkFun(BVUrem, {a1, a2});
}

SymRef FSBVLogic::mkBVShlSym(SRef sr) {
    if (not isBitVectorSort(sr)) {
        throw OsmtApiException("mkBVSHL called for unrelated sort " + printSort(sr));
    }
    return declareFun_NoScoping_LeftAssoc(tk_bvshl, sr, {sr, sr});
}

PTRef FSBVLogic::mkBVShl(PTRef a, PTRef shift) {
    SymRef BVSHL = mkBVShlSym(getSortRef(a));
    std::string why;
    if (not typeCheck(BVSHL, {a, shift}, why)) {
        throw OsmtApiException(why);
    }
    return mkFun(BVSHL, {a, shift});
}

SymRef FSBVLogic::mkBVLshrSym(SRef sr) {
    if (not isBitVectorSort(sr)) {
        throw OsmtApiException("mkBVLSHR called for unrelated sort " + printSort(sr));
    }
    return declareFun_NoScoping_LeftAssoc(tk_bvlshr, sr, {sr, sr});
}

PTRef FSBVLogic::mkBVLshr(PTRef a, PTRef shift) {
    SymRef BVLSHR = mkBVLshrSym(getSortRef(a));
    std::string why;
    if (not typeCheck(BVLSHR, {a, shift}, why)) {
        throw OsmtApiException(why);
    }
    return mkFun(BVLSHR, {a, shift});
}

SymRef FSBVLogic::mkBVUltSym(SRef sr) {
    if (not isBitVectorSort(sr)) {
        throw OsmtApiException("mkBVULT called for unrelated sort " + printSort(sr));
    }
    return declareFun_NoScoping_LeftAssoc(tk_bvult, sort_BOOL, {sr, sr});
}

PTRef FSBVLogic::mkBVUlt(PTRef lhs, PTRef rhs) {
    SymRef BVULT = mkBVUltSym(getSortRef(lhs));
    std::string why;
    if (not typeCheck(BVULT, {lhs, rhs}, why)) {
        throw OsmtApiException(why);
    }
    return mkFun(BVULT, {lhs, rhs});
}


PTRef FSBVLogic::insertTerm(SymRef sym, vec<PTRef> && args) {
    if (isBVConcat(sym)) {
        return mkBVConcat(args[0], args[1]);
    } else if (isBVAdd(sym)) {
        return mkBVAdd(std::move(args));
    } else if (isBVNeg(sym)) {
        return mkBVNeg(args[0]);
    } else if (isBVNot(sym)) {
        return mkBVNot(args[0]);
    } else if (isBVAnd(sym)) {
        return mkBVAnd(std::move(args));
    } else if (isBVOr(sym)) {
        return mkBVOr(std::move(args));
    } else if (isBVMul(sym)) {
        return mkBVMul(std::move(args));
    } else if (isBVUdiv(sym)) {
        return mkBVUdiv(args[0], args[1]);
    } else if (isBVUrem(sym)) {
        return mkBVUrem(args[0], args[1]);
    } else if (isBVShl(sym)) {
        return mkBVShl(args[0], args[1]);
    } else if (isBVLshr(sym)) {
        return mkBVLshr(args[0], args[1]);
    } else if (isBVUlt(sym)) {
        return mkBVUlt(args[0], args[1]);
    } else if (isBVConst(sym)) {
        return mkBVConst(sym);
    } else {
        return Logic::insertTerm(sym, std::move(args));
    }
}

PTRef FSBVLogic::resolveTerm(char const * s, vec<PTRef> && args, SRef returnSort, SymbolMatcher symbolMatcher) {
    if (s == std::string(tk_bvconcat)) {
        if (args.size() != 2) {
            throw OsmtApiException(std::string(tk_bvconcat) + " requires exactly two arguments");
        }
        return mkBVConcat(args[0], args[1]);
    } else if (s == std::string(tk_bvadd)) {
        return mkBVAdd(std::move(args));
    } else if (s == std::string(tk_bvneg)) {
        if (args.size() != 1) {
            throw OsmtApiException(std::string(tk_bvneg) + " requires exactly one argument");
        }
        return mkBVNeg(args[0]);
    } else if (s == std::string(tk_bvnot)) {
        if (args.size() != 1) {
            throw OsmtApiException(std::string(tk_bvnot) + " require exactly one argument");
        }
        return mkBVNot(args[0]);
    } else if (s == std::string(tk_bvand)) {
        return mkBVAnd(std::move(args));
    } else if (s == std::string(tk_bvor)) {
        return mkBVOr(std::move(args));
    } else if (s == std::string(tk_bvmul)) {
        return mkBVMul(std::move(args));
    } else if (s == std::string(tk_bvudiv)) {
        if (args.size() != 2) {
            throw OsmtApiException(std::string(tk_bvudiv) + " requires exactly two arguments");
        }
        return mkBVUdiv(args[0], args[1]);
    } else if (s == std::string(tk_bvurem)) {
        if (args.size() != 2) {
            throw OsmtApiException(std::string(tk_bvurem) + " requires exactly two arguments");
        }
        return mkBVUrem(args[0], args[1]);
    } else if (s == std::string(tk_bvshl)) {
        if (args.size() != 2) {
            throw OsmtApiException(std::string(tk_bvshl) + " requires exactly two arguments");
        }
        return mkBVShl(args[0], args[1]);
    } else if (s == std::string(tk_bvlshr)) {
        if (args.size() != 2) {
            throw OsmtApiException(std::string(tk_bvlshr) + " requires exactly two arguments");
        }
        return mkBVLshr(args[0], args[1]);
    } else if (s == std::string(tk_bvult)) {
        if (args.size() != 2) {
            throw OsmtApiException(std::string(tk_bvult) + " requires exactly two arguments");
        }
        return mkBVUlt(args[0], args[1]);
    } else if (std::string(s).rfind(BVHexPrefix, 0) == 0) {
        return mkBVConstFromHex(s);
    } else if (std::string(s).rfind(BVBinPrefix, 0) == 0) {
        return mkBVConstFromBin(s);
    }
    else {
        return Logic::resolveTerm(s, std::move(args), returnSort, symbolMatcher);
    }
}
