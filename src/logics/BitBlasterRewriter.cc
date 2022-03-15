/*
 * Copyright (c) 2008 - 2012, Roberto Bruttomesso
 * Copyright (c) 2012 - 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

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

void BitBlasterConfig::bbConcat(PTRef concat_tr) {
    Pterm const & concat = logic.getPterm(concat_tr);
    BVRef a = store[concat[0]];
    BVRef b = store[concat[1]];
    auto size = store[a].size() + store[b].size();
    assert(logic.getRetSortBitWidth(concat_tr) == static_cast<BitWidth_t>(size));
    vec<PTRef> result;
    result.capacity(size);
    for (PTRef tr : store[b]) {
        result.push(tr);
    }
    for (PTRef tr : store[a]) {
        result.push(tr);
    }
    // Save result and return
    store.newBvector(result, concat_tr);
}

void BitBlasterConfig::bbFlip(PTRef flip_tr) {
    BVRef a = store[logic.getPterm(flip_tr)[0]];
    auto size = store[a].size();
    vec<PTRef> result;
    result.capacity(size);
    for (PTRef tr : store[a]) {
        result.push(logic.mkNot(tr));
    }
    // Save result and return
    store.newBvector(result, flip_tr);
}

void BitBlasterConfig::bbNot(PTRef not_tr) {
    BVRef a = store[logic.getPterm(not_tr)[0]];
    auto size = store[a].size();
    vec<PTRef> result;
    result.growTo(size, logic.getTerm_false());
    vec<PTRef> args;
    for (PTRef tr : store[a]) {
        args.push(tr);
    }
    result[0] = logic.mkNot(logic.mkOr(args));
    // Save result and return
    store.newBvector(result, not_tr);
}

void BitBlasterConfig::bbAnd(PTRef and_tr) {
    Pterm const & and_ = logic.getPterm(and_tr);
    BVRef a = store[and_[0]];
    BVRef b = store[and_[1]];
    assert(store[a].size() == store[b].size());
    auto size = store[a].size();
    vec<PTRef> result;
    result.capacity(size);
    for (auto i = 0; i < size; i++) {
        result.push(logic.mkAnd(store[a][i], store[b][i]));
    }
    store.newBvector(result, and_tr);
}

void BitBlasterConfig::bbOr(PTRef and_tr) {
    Pterm const & and_ = logic.getPterm(and_tr);
    BVRef a = store[and_[0]];
    BVRef b = store[and_[1]];
    assert(store[a].size() == store[b].size());
    auto size = store[a].size();
    vec<PTRef> result;
    result.capacity(size);
    for (auto i = 0; i < size; i++) {
        result.push(logic.mkOr(store[a][i], store[b][i]));
    }
    store.newBvector(result, and_tr);
}

void BitBlasterConfig::bbUdiv(PTRef div_tr) {
    Pterm const & div = logic.getPterm(div_tr);
    BVRef dividend = store[div[0]];
    BVRef divisor = store[div[1]];
    assert(store[divisor].size() == store[dividend].size());

    auto size = store[divisor].size();
    vec<PTRef> result;
    result.growTo(size);

    vec<PTRef> minuend;
    minuend.capacity(size);

    // Initialize minuend as 0..0 q[n-1]
    minuend.push(store[dividend][size - 1]);
    for (int i = 1; i < size; i ++) {
        minuend.push(logic.getTerm_false());
    }

    // Main loop
    for (int i = size - 1; i >= 0; i --) {
        // Compute result[ i ] = !(minuend < divisor);
        PTRef lt_prev = PTRef_Undef;
        for (int j = 0; j < size; j ++) {
            // Produce ~l[j] & r[j]
            PTRef not_l = logic.mkNot(minuend[j]);
            PTRef lt_this = logic.mkAnd(not_l, store[divisor][j]);
            // Produce l[j] <-> r[j]
            PTRef eq_this = logic.mkEq(minuend[j], store[divisor][j]);
            if (lt_prev != PTRef_Undef) {
                lt_prev = logic.mkOr(lt_this, logic.mkAnd(eq_this, lt_prev));
            } else {
                lt_prev = lt_this;
            }
        }

        assert( lt_prev != PTRef_Undef);

        result[i] = logic.mkNot(lt_prev);
        PTRef bit_i = result[i];

        // Construct subtrahend
        vec<PTRef> subtrahend;
        subtrahend.capacity(size);
        for (int j = 0; j < size; j ++) {
            subtrahend.push(logic.mkAnd(bit_i, store[divisor][j]));
        }

        // Subtract and store in minuend
        PTRef carry = PTRef_Undef;
        for (int j = 0; j < minuend.size(); j++) {
            PTRef bit_1 = minuend[j];
            PTRef bit_2 = subtrahend[j];

            PTRef bit_2_neg = logic.mkNot(bit_2);
            PTRef xor_1 = logic.mkXor(bit_1, bit_2_neg);
            PTRef and_1 = logic.mkAnd(bit_1, bit_2_neg);

            if (carry != PTRef_Undef) {
                PTRef xor_2 = logic.mkXor(xor_1, carry);
                PTRef and_2 = logic.mkAnd(xor_1, carry);
                carry = logic.mkOr(and_1, and_2);
                minuend[j] = xor_2;
            } else {
                carry = and_1;
                minuend[j] = xor_1;
            }
        }

        carry = PTRef_Undef;

        // Adds one, if bit_i is one
        for (int j = 0; j < minuend.size(); j++) {
            PTRef bit_1 = minuend[j];
            PTRef bit_2 = j == 0 ? logic.getTerm_true() : logic.getTerm_false();

            PTRef xor_1 = logic.mkXor(bit_1, bit_2);
            PTRef and_1 = logic.mkAnd(bit_1, bit_2);

            if (carry != PTRef_Undef) {
                PTRef xor_2 = logic.mkXor(xor_1, carry);
                PTRef and_2 = logic.mkAnd(xor_1, carry);
                carry = logic.mkOr(and_1, and_2);
                minuend[j] = xor_2;
            } else {
                carry = and_1;
                minuend[j] = xor_1;
            }
        }

        if (i > 0) {
            // Prepare new minuend
            //
            //                M[i-1]
            //
            // O[2] O[1] O[0]
            //      N[2] N[1] N[0]
            //
            for (int j = size - 1 ; j >= 1 ; j --) {
                minuend[j] = minuend[j - 1];
            }
            minuend[0] = store[dividend][i - 1];
        }
    }

    // Save result and return
    store.newBvector(result, div_tr);
}

void BitBlasterConfig::bbUrem(PTRef rem_tr) {
    Pterm const & rem = logic.getPterm(rem_tr);

    vec<PTRef> minuend;
    BVRef dividend = store[rem[0]];
    BVRef divisor = store[rem[1]];

    assert(store[divisor].size() == store[dividend].size());

    auto size = store[divisor].size();

    vec<PTRef> result;
    result.growTo(size);

    // Initialize minuend as 0..0 q[n-1]
    minuend.push(store[dividend][size-1]);
    for (int i = 1; i < size; i ++) {
        minuend.push(logic.getTerm_false());
    }

    // Main loop
    for (int i = size - 1; i >= 0; i --) {
        // Compute result[i] = !(minuend < divisor);
        PTRef lt_prev = PTRef_Undef;
        for (int j = 0; j < size; j ++) {
            // Produce ~l[j] & r[j]
            PTRef not_l   = logic.mkNot(minuend[j]);
            PTRef lt_this = logic.mkAnd(not_l, store[divisor][j]);
            // Produce l[j] <-> r[j]
            PTRef eq_this = logic.mkEq(minuend[j], store[divisor][j]);
            if (lt_prev != PTRef_Undef) {
                lt_prev = logic.mkOr(lt_this, logic.mkAnd(eq_this, lt_prev));
            } else {
                lt_prev = lt_this;
            }
        }

        PTRef bit_i = logic.mkNot(lt_prev);

        // Construct subtrahend
        vec<PTRef> subtrahend;
        for (int j = 0; j < size; j ++) {
            subtrahend.push(logic.mkAnd(bit_i, store[divisor][j]));
        }

        // Subtract and store in minuend
        PTRef carry = PTRef_Undef;

        for (int j = 0; j < minuend.size(); j++) {
            PTRef bit_1 = minuend[j];
            PTRef bit_2 = subtrahend[j];

            PTRef bit_2_neg = logic.mkNot(bit_2);
            PTRef xor_1 = logic.mkXor(bit_1, bit_2_neg);
            PTRef and_1 = logic.mkAnd(bit_1, bit_2_neg);

            if (carry != PTRef_Undef) {
                PTRef xor_2 = logic.mkXor(xor_1, carry);
                PTRef and_2 = logic.mkAnd(xor_1, carry);
                carry = logic.mkOr(and_1, and_2);
                minuend[j] = xor_2;
            } else {
                carry = and_1;
                minuend[j] = xor_1;
            }
        }

        carry = PTRef_Undef;

        // Adds one, if bit_i is one
        for (int j = 0; j < minuend.size(); j++) {
            PTRef bit_1 = minuend[j];
            PTRef bit_2 = j == 0 ? logic.getTerm_true() : logic.getTerm_false();

            PTRef xor_1 = logic.mkXor(bit_1, bit_2);
            PTRef and_1 = logic.mkAnd(bit_1, bit_2);

            if (carry != PTRef_Undef) {
                PTRef xor_2 = logic.mkXor(xor_1, carry);
                PTRef and_2 = logic.mkAnd(xor_1, carry);
                carry = logic.mkOr(and_1, and_2);
                minuend[j] = xor_2;
            } else {
                carry = and_1;
                minuend[j] = xor_1;
            }
        }

        if (i > 0) {
            // Prepare new minuend
            //                M[i-1]
            //
            // O[2] O[1] O[0]
            //      N[2] N[1] N[0]
            //
            for (int j = size - 1; j >= 1; j --) {
                minuend[j] = minuend[j - 1];
            }
            minuend[0] = store[dividend][i - 1];
        } else {
            for (int j = 0 ; j < size; j ++) {
                result[j] = minuend[j];
            }
        }
    }

    // Save result
    store.newBvector(result, rem_tr);
}

auto ls_read = [](int s, int i, std::vector<vec<PTRef>> const & table) { return table[s+1][i]; };
auto ls_write = [](int s, int i, PTRef tr, std::vector<vec<PTRef>> & table) { table[s+1][i] = tr; };

void BitBlasterConfig::bbShl(PTRef shl_tr) {
    Pterm const & shl = logic.getPterm(shl_tr);
    // Allocate new result
    vec<PTRef> result;

    vec<PTRef> acc;

    BVRef a = store[shl[0]];
    BVRef b = store[shl[1]];

    assert(store[a].size() == store[b].size());
    int size = store[a].size();
    if (not opensmt::isPowOfTwo(size)) {
        throw OsmtApiException("shl not supported for non-power-of-two bit widths currently");
    }

    int l = size;
    int n = opensmt::getLogFromPowOfTwo(size);

    std::vector<vec<PTRef>> ls;
    for (int s = -1; s <= n-1; s++) {
        ls.emplace_back();
        for (int i = 0; i < l; i++) {
            ls.back().push(PTRef_Undef);
        }
    }


    for (int i = 0; i < l; i++) {
        ls_write(-1, i, store[a][i], ls);
    }

    for (int s = 0; s <= n-1; s++) {
        for (int i = 0; i < l; i++) {
            if (i >= (1 << s)) {// i >= 2^s
                ls_write(s, i, logic.mkIte(store[b][s], ls_read(s - 1, i - (1 << s), ls), ls_read(s - 1, i, ls)), ls);
            } else {
                ls_write(s, i, logic.mkIte(store[b][s], logic.getTerm_false(), ls_read(s - 1, i, ls)), ls);
            }
        }
    }
    store.newBvector(ls.back(), shl_tr);
}

void BitBlasterConfig::bbLshr(PTRef lshr_tr) {
    bool arith = false;
    Pterm const & lshr = logic.getPterm(lshr_tr);
    // Allocate new result
    vec<PTRef> result;

    vec<PTRef> acc;

    BVRef a = store[lshr[0]];
    BVRef b = store[lshr[1]];

    assert(store[a].size() == store[b].size());
    auto size = store[a].size();
    if (not opensmt::isPowOfTwo(size)) {
        throw OsmtApiException("lshr not supported for non-power-of-two bit widths currently");
    }

    int l = size;
    int n = opensmt::getLogFromPowOfTwo(size);

    std::vector<vec<PTRef>> ls;
    for (int s = -1; s <= n-1; s++) {
        ls.emplace_back();
        for (int i = 0; i < l; i++)
            ls.back().push(PTRef_Undef);
    }

    for (int i = 0; i < l; i++)
        ls_write(-1, i, store[a][i], ls);

    PTRef fill = arith ? store[a].msb() : logic.getTerm_false();
    for (int s = 0; s <= n-1; s++) {
        for (int i = 0; i < l; i++) {
            if (i + (1 << s) <= l-1) {// i + 2^s <= l-1
                ls_write(s, i, logic.mkIte(store[b][s], ls_read(s - 1, i + (1 << s), ls), ls_read(s - 1, i, ls)), ls);
            } else {
                ls_write(s, i, logic.mkIte(store[b][s], fill, ls_read(s - 1, i, ls)), ls);
            }
        }
    }

    store.newBvector(ls.back(), lshr_tr);
}
