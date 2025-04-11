/*
 *  Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 */

#include "Translations.h"

namespace opensmt {
LAPoly ptrefToPoly(PTRef const op, ArithLogic & logic) {
    assert(logic.isLeq(op) or logic.isEquality(op));
    assert(logic.getPterm(op).size() == 2);
    LAPoly poly;
    PTRef const lhs = logic.getPterm(op)[0];
    PTRef const rhs = logic.getPterm(op)[1];
    PTRef const polyTerm = lhs == logic.getZeroForSort(logic.getSortRef(lhs)) ? rhs : logic.mkMinus(rhs, lhs);
    assert(logic.isLinearTerm(polyTerm));
    if (logic.isLinearFactor(polyTerm)) {
        auto [var, c] = logic.splitTermToVarAndConst(polyTerm);
        poly.addTerm(var, logic.getNumConst(c));
    } else {
        assert(logic.isPlus(polyTerm));
        for (PTRef const factor : logic.getPterm(polyTerm)) {
            auto [var, c] = logic.splitTermToVarAndConst(factor);
            poly.addTerm(var, logic.getNumConst(c));
        }
    }
    return poly;
}

PTRef polyToPTRef(LAPoly & poly, ArithLogic & logic, SRef const type) {
    if (type == logic.getSort_int()) {
        // Ensure the polynomial does not have any fractional coefficients
        Real multiplyBy = 1;
        for (auto const & [var, coeff] : poly) {
            if (var == PTRef_Undef) { continue; }
            if (coeff.isInteger()) { continue; }
            multiplyBy = lcm(multiplyBy, coeff.get_den());
        }
        if (not multiplyBy.isOne()) { poly.multiplyBy(multiplyBy); }
    }
    vec<PTRef> args;
    args.capacity(static_cast<int>(poly.size()));
    for (auto const & [var, coeff] : poly) {
        assert(not coeff.isZero());
        if (var == PTRef_Undef) {
            args.push(logic.mkConst(type, coeff));
        } else {
            args.push(coeff.isOne() ? var : logic.mkTimes(logic.mkConst(type, coeff), var));
        }
    }
    return logic.mkPlus(std::move(args)); // TODO: Can we use non-simplifying versions of mkPlus/mkTimes?
}

} // namespace opensmt