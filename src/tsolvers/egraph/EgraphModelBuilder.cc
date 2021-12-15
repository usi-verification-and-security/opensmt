/*
 *  Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Copyright (c) 2021, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 */

#include "EgraphModelBuilder.h"

#include "ArithLogic.h"
#include "ModelBuilder.h"

Map<ERef, PTRef, ERefHash> EgraphModelBuilder::computeNumericValues(ModelBuilder const & model) const {
    ArithLogic & arithLogic = dynamic_cast<ArithLogic &>(logic);
    Map<ERef, PTRef, ERefHash> updatedValues;
    std::unordered_set<ERef, ERefHash> delayedNumericTerms;
    FastRational maxModelValue = 0;
    auto updateMaxValue = [&maxModelValue](FastRational const & newVal) {
        if (newVal > maxModelValue) { maxModelValue = newVal; }
    };
    for (ERef eref : enode_store.getTermEnodes()) {
        ERef root = values.getValue(eref);
        PTRef ptref_root = enode_store.getPTRef(root);
        if (not arithLogic.yieldsSortNum(ptref_root)) {
            continue;
        }
        if (updatedValues.has(root)) { continue; }
        if (arithLogic.isNumConst(ptref_root)) {
            updatedValues.insert(root, ptref_root);
            updateMaxValue(arithLogic.getNumConst(ptref_root));
            continue;
        }
        PTRef ptref = enode_store.getPTRef(eref);
        if (logic.isVar(ptref) and model.hasVarVal(ptref)) {
            PTRef value = model.getVarVal(ptref);
            assert(arithLogic.isNumConst(value));
            updatedValues.insert(root, value);
            updateMaxValue(arithLogic.getNumConst(value));
            delayedNumericTerms.erase(root);
            continue;
        }
        delayedNumericTerms.insert(root);
        // continue with next Enode
    }
    for (ERef delayedTerm : delayedNumericTerms) {
        FastRational nextValue = maxModelValue + 1;
        SRef sort = logic.getSortRef(getEnode(delayedTerm).getTerm());
        if (arithLogic.isSortInt(sort)) {
            nextValue = nextValue.floor();
        }
        updatedValues.insert(delayedTerm, arithLogic.mkConst(sort, nextValue));
        maxModelValue = nextValue;
    }
    return updatedValues;
}

/**
 * Add an evaluation for the function symbol of orig_tr using the value of target_er
 * @param modelBuilder The model builder
 * @param orig_tr the original pterm reference (with arity > 0)
 * @param target_er the target enode reference
 * @param substs the substitutions (used for obtaining values for the arguments of orig_tr
 */
void EgraphModelBuilder::addTheoryFunctionEvaluation(ModelBuilder & modelBuilder, PTRef orig_tr, ERef target_er) {
    ERef orig_er = enode_store.getERef(orig_tr);
    Enode const & orig_enode = getEnode(orig_er);
    assert(orig_enode.getSize() > 0);
    vec<PTRef> vals; vals.capacity(orig_enode.getSize());
    for (ERef child_er : orig_enode) {
        PTRef child_tr = enode_store.getPTRef(child_er);
        vals.push(getAbstractValueForERef(child_er,logic.getSortRef(child_tr)));
    }
    modelBuilder.addToTheoryFunction(logic.getSymRef(orig_tr), vals, getAbstractValueForERef(target_er, logic.getSortRef(orig_tr)));
}

void EgraphModelBuilder::fill(ModelBuilder & modelBuilder) && {
    if (hasArithmetic()) {
        auto numericValues = computeNumericValues(modelBuilder);
        for (auto [key, val] : numericValues.getKeysAndVals()) {
            if (val != PTRef_Undef) {
                assert(not rootValues.has(key));
                rootValues.insert(key, val);
            }
        }
    }
    for (ERef er : enode_store.getTermEnodes()) {
        PTRef tr = enode_store.getPTRef(er);

        if (logic.hasSortBool(tr) and (not logic.isUP(tr))) {
            continue; // The Boolean return sorted terms that are not uninterpreted predicates come from the SAT solver
        }

        // Check that enode_store's PTRef -> ERef conversion is consistent
        assert(([&](PTRef tr) { ERef tmp; enode_store.peekERef(tr, tmp); return tmp == er; })(tr));

        assert(not logic.isIte(tr));
        if (((logic.isVar(tr) or logic.isConstant(tr))) and logic.yieldsSortUninterpreted(tr)) {
            PTRef val_tr = getAbstractValueForERef(er, logic.getSortRef(tr));
            modelBuilder.addVarValue(tr, val_tr);
        } else if (logic.isVar(tr) and not modelBuilder.hasVarVal(tr)) {
            PTRef val_tr = getAbstractValueForERef(er, logic.getSortRef(tr));
            modelBuilder.addVarValue(tr, val_tr);
        } else if (logic.isUF(tr)) {
            addTheoryFunctionEvaluation(modelBuilder, tr, er);
        }
    }
}

/**
 * Get the abstract value (name of an element of the universe) corresponding to er.
 * If er is ERef_Undef, use the default element for the sort sr
 * @param er
 * @param sr the sort of er
 * @return
 */
PTRef EgraphModelBuilder::getAbstractValueForERef(ERef er, SRef sr) {

    if (er == ERef_Undef) {
        return logic.getDefaultValuePTRef(sr);
    }

    ERef val_er = values.getValue(er);
    PTRef val_tr = enode_store.getPTRef(val_er);
    assert(sr == logic.getSortRef(val_tr));

    if (logic.isConstant(val_tr)) {
        return val_tr;
    }
    if (rootValues.has(val_er)) {
        return rootValues[val_er];
    }
    std::stringstream ss;
    ss << Logic::s_abstract_value_prefix << values.getValueIndex(val_er);
    PTRef newVal = logic.mkConst(sr, ss.str().c_str());
    rootValues.insert(val_er, newVal);
    return newVal;
}
