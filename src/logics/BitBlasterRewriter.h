//
// Created by prova on 09.03.22.
//

#ifndef OPENSMT_BITBLASTERREWRITER_H
#define OPENSMT_BITBLASTERREWRITER_H

#include "Rewriter.h"
#include "FSBVLogic.h"
#include "bvsolver/BVStore.h"
#include "OsmtInternalException.h"

class BitBlasterConfig : public DefaultRewriterConfig {
    FSBVLogic & logic;
    BVStore & store;

    static inline const std::string BitVectorVarPrefix = ".bv";

    PTRef bbEquality(PTRef eq_tr);
    PTRef bbDisequality(PTRef diseq_tr);
    PTRef bbUlt(PTRef ult_tr);
    void bbConstant(PTRef tr);
    void bbMul(PTRef mul_tr);
    void bbVar(PTRef var_tr);
    void bbAdd(PTRef add_tr);

    void notImplemented(PTRef tr) { throw OsmtInternalException(std::string("Not implemented: ") + logic.getSymName(tr)); }

    void bbConcat(PTRef tr) { notImplemented(tr); }
    void bbNot(PTRef tr) { notImplemented(tr); }
    void bbNeg(PTRef tr) { notImplemented(tr); }
    void bbAnd(PTRef tr) { notImplemented(tr); }
    void bbOr(PTRef tr) { notImplemented(tr); }
    void bbUdiv(PTRef tr) { notImplemented(tr); }
    void bbUrem(PTRef tr) { notImplemented(tr); }
    void bbShl(PTRef tr) { notImplemented(tr); }
    void bbLshr(PTRef tr) { notImplemented(tr); }

public:
    BitBlasterConfig(FSBVLogic & logic, BVStore & bvStore) : logic(logic), store(bvStore) {}

    PTRef rewrite(PTRef tr) override {
        SymRef sr = logic.getSymRef(tr);
        if (logic.isEquality(sr) and logic.isBitVectorSort(logic.getUniqueArgSort(sr))) {
            return bbEquality(tr);
        } else if (logic.isDisequality(sr) and logic.isBitVectorSort(logic.getUniqueArgSort(sr))) {
            return bbDisequality(tr);
        } else if (logic.isBVUlt(sr)) {
            return bbUlt(tr);
        } else if (logic.isBVConst(sr)) {
            bbConstant(tr);
        } else if (logic.isBVMul(sr)) {
            bbMul(tr);
        } else if (logic.isBVVar(sr)) {
            bbVar(tr);
        } else if (logic.isBVAdd(sr)) {
            bbAdd(tr);
        } else if (logic.isBVConcat(sr)) {
            bbConcat(tr);
        } else if (logic.isBVNot(sr)) {
            bbNot(tr);
        } else if (logic.isBVNeg(sr)) {
            bbNeg(tr);
        } else if (logic.isBVAnd(sr)) {
            bbAnd(tr);
        } else if (logic.isBVOr(sr)) {
            bbOr(tr);
        } else if (logic.isBVUdiv(sr)) {
            bbUdiv(tr);
        } else if (logic.isBVUrem(sr)) {
            bbUrem(tr);
        } else if (logic.isBVShl(sr)) {
            bbShl(tr);
        } else if (logic.isBVLshr(sr)) {
            bbLshr(tr);
        }
        return tr;
    }
};

class BitBlasterRewriter : Rewriter<BitBlasterConfig> {
    BitBlasterConfig config;
    BVStore store;
public:
    BitBlasterRewriter(FSBVLogic & logic) : Rewriter<BitBlasterConfig>(logic, config), config(logic, store) {}
    PTRef rewrite(PTRef tr) override { return Rewriter<BitBlasterConfig>::rewrite(tr); }
    std::unordered_map<PTRef, PTRef, PTRefHash> getBitBlastedTermToBitVectorTermMap() const {
        std::unordered_map<PTRef, PTRef, PTRefHash> map;
        for (PTRef tr : store.getBitVectorTerms()) {
            BVRef br = store.getFromPTRef(tr);
            for (int i = 0; i < store[br].size(); i++) {
                PTRef bitBlastedTerm = store[br][i];
                map.insert({bitBlastedTerm, tr});
            }
        }
        return map;
    }
};

#endif //OPENSMT_BITBLASTERREWRITER_H
