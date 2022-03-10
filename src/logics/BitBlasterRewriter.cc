//
// Created by prova on 09.03.22.
//

#include "BitBlasterRewriter.h"
#include <cmath>

PTRef BitBlasterConfig::bbEquality(PTRef eq_tr) {
    Pterm & eq = logic.getPterm(eq_tr);
    BVRef lhs = store[eq[0]];
    BVRef rhs = store[eq[1]];

    assert(store[lhs].size() == store[rhs].size());
    int size = store[lhs].size();
    // Produce the result
    vec<PTRef> result_args;
    result_args.capacity(size);

    for (int i = 0; i < size; ++ i) {
        result_args.push(logic.mkEq(store[lhs][i], store[rhs][i]));
    }
    PTRef res = logic.mkAnd(result_args);
    return res;
}

PTRef BitBlasterConfig::bbDisequality(PTRef diseq_tr) {
    Pterm & diseq = logic.getPterm(diseq_tr);
    vec<PTRef> args;
    args.capacity((diseq.size() + (diseq.size()-1))/2);
    for (int i = 0; i < diseq.size(); i++) {
        for (int j = i+1; j < diseq.size(); j++) {
            args.push(logic.mkNot(bbEquality(logic.mkEq(diseq[i], diseq[j]))));
        }
    }
    return logic.mkAnd(args);
}

PTRef BitBlasterConfig::bbUlt(PTRef ult_tr) {
    Pterm const & ult = logic.getPterm(ult_tr);
    BVRef lhs = store[ult[0]];
    BVRef rhs = store[ult[1]];
    assert(store[lhs].size() == store[rhs].size() and store[lhs].size() > 0);
    PTRef isLessThanUpToHere = PTRef_Undef;
    for (int i = 0; i < store[lhs].size(); i++) {
        // ~lhs[i] & rhs[i]
        PTRef bitLessThan = logic.mkAnd(logic.mkNot(store[lhs][i]), store[rhs][i]);
        // Produce l[i] <-> r[i]
        PTRef bitEq = logic.mkEq(store[lhs][i], store[rhs][i]);
        isLessThanUpToHere = (i > 0) ? logic.mkOr(bitLessThan, logic.mkAnd(bitEq, isLessThanUpToHere)) : bitLessThan;
    }
    return isLessThanUpToHere;
}

void BitBlasterConfig::bbConstant(PTRef tr) {
    auto bw = logic.getRetSortBitWidth(tr);

    vec<PTRef> asgns;
    asgns.growTo(bw, logic.getTerm_false());

    if (logic.isTrue(tr)) {
        asgns[0] = logic.getTerm_true();
    } else if (logic.isFalse(tr)) {
        ; // Already ok
    } else {
        const std::string value = logic.getSymName(tr);
        assert((value.length()-2) == static_cast<unsigned>(bw)); // in binary
        for (unsigned int i = 0 ; i < bw; ++i) {
            unsigned int idx = bw - i + 1;
            assert(value[idx] == '1' or value[idx] == '0');
            asgns[i] = value[idx] == '1' ? logic.getTerm_true() : logic.getTerm_false();
        }
    }
    store.newBvector(asgns, tr);
}

void BitBlasterConfig::bbMul(PTRef mul_tr) {

    Pterm const & mul = logic.getPterm(mul_tr);
    BVRef a = store[mul[0]];
    BVRef b = store[mul[1]];
    assert(store[a].size() == store[b].size());
    int size = store[a].size();

    // Allocate new result
    vec<PTRef> acc;
    acc.capacity(size);
    vec<PTRef> result;
    result.capacity(size);

    // Compute term a_{i-1}*b_{j-1} ... a_0*b_0
    for (int i = 0; i < size; ++ i) {
        acc[i] = logic.mkAnd(store[b][0], store[a][i]);
    }
    // Multi-arity adder
    for (int i = 1; i < size; i ++) {
        vec<PTRef> addend;
        addend.capacity(size);
        // Push trailing 0s
        for (int j = 0; j < i; ++ j) {
            addend.push(logic.getTerm_false());
        }
        // Compute term a_{i-1}*b_i ... a_0*b_i 0 ... 0
        for (int j = 0; j < size - i; j++) {
            addend.push(logic.mkAnd(store[b][i], store[a][j]));
        }

        // Accumulate computed term
        PTRef carry = PTRef_Undef;

        for (int k = 0; k < size ; k++) {
            PTRef bit_1 = acc[k];
            PTRef bit_2 = addend[k];
            assert(bit_1 != PTRef_Undef);
            assert(bit_2 != PTRef_Undef);

            PTRef xor_1 = logic.mkXor(bit_1, bit_2);
            PTRef and_1 = logic.mkAnd(bit_1, bit_2);

            if (carry != PTRef_Undef) {
                PTRef xor_2 = logic.mkXor(xor_1, carry);
                PTRef and_2 = logic.mkAnd(xor_1, carry);
                carry = logic.mkOr(and_1, and_2);
                if (i == size - 1)
                    result.push(xor_2);
                else
                    acc[k] = xor_2;
            } else {
                carry = and_1;
                if (i == size - 1)
                    result.push(xor_1);
                else
                    acc[k] = xor_1;
            }
        }
    }
    store.newBvector(result, mul_tr);
}

void BitBlasterConfig::bbVar(PTRef var_tr) {
    // Allocate new result
    auto size = static_cast<int>(logic.getRetSortBitWidth(var_tr));
    vec<PTRef> vars;
    vars.capacity(size);

    int targetLength = static_cast<int>(std::log10(size))+1;
    auto zeroPadNumber = [](int number, unsigned long targetLength) {
        std::string s = std::to_string(number);
        return std::string(targetLength - std::min(targetLength, s.length()), '0') + s;
    };

    for (int i = 0; i < size; ++i) {
        std::string bitName = BitVectorVarPrefix + std::to_string(var_tr.x) + '_' + zeroPadNumber(i, targetLength);
        vars.push(logic.mkBoolVar(bitName.c_str()));
    }
    store.newBvector(vars, var_tr);
}

void BitBlasterConfig::bbAdd(PTRef add_tr) {
    Pterm const & add = logic.getPterm(add_tr);
    BVRef a = store[add[0]];
    BVRef b = store[add[1]];

    assert(store[a].size() == store[b].size());
    int size = store[a].size(); // the bit width

    // Allocate new result
    vec<PTRef> result;

    PTRef carry = PTRef_Undef;

    for (int i = 0 ; i < size; i++) {
        PTRef bit_1 = store[a][i];
        PTRef bit_2 = store[b][i];
        assert(bit_1 != PTRef_Undef);
        assert(bit_2 != PTRef_Undef);

        PTRef xor_1 = logic.mkXor(bit_1, bit_2);
        PTRef and_1 = logic.mkAnd(bit_1, bit_2);

        if (carry != PTRef_Undef) {
            PTRef xor_2 = logic.mkXor(xor_1, carry);
            PTRef and_2 = logic.mkAnd(xor_1, carry);
            carry = logic.mkOr(and_1, and_2);
            result.push(xor_2);
        } else {
            carry = and_1;
            result.push(xor_1);
        }
    }

    // Save result and return
    store.newBvector(result, add_tr);
}