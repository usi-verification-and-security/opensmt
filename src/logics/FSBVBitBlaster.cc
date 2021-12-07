/*
 * Copyright (c) 2021, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "FSBVBitBlaster.h"

vec<PTRef> FSBVBitBlaster::getBVVars(std::string const & base, BitWidth_t width) {
    vec<PTRef> vars;
    vars.growTo(width);
    for (unsigned int i = 0; i < width; i++) {
        std::string bit_name = base + std::to_string(i) + "_" + std::to_string(bs.size());
        vars[i] = logic.mkBoolVar(bit_name.c_str());
    }
    return vars;
}

PTRef FSBVBitBlaster::bbPredicate(PTRef tr)  {
    SymRef sr = logic.getSymRef(tr);

    if (logic.isEquality(sr)) {
        BVRef lhs = bbTerm(logic.getPterm(tr)[0]);
        BVRef rhs = bbTerm(logic.getPterm(tr)[1]);
        assert( bs[lhs].size( ) == bs[rhs].size( ) );

        // Produce the result
        vec<PTRef> result_args;
        for ( int i = 0 ; i < bs[lhs].size() ; i ++ )
        {
            result_args.push(logic.mkEq(bs[lhs][i], bs[rhs][i]));
        }
        PTRef res = logic.mkAnd(result_args);
        return res;
    } else if (logic.isDisequality(sr)) {
        notImplemented(tr);
        return PTRef_Undef;
    } else if (logic.isBVUlt(sr)) {
        return bbUlt(tr);
    } else {
        throw OsmtApiException(std::string("Attempting to top-level BitBlast a non-predicate ") + logic.getSymName(sr));
    }
}

BVRef FSBVBitBlaster::bbTerm(PTRef tr) {
    assert(logic.yieldsSortBV(tr));
    if (bs.has(tr))
        return bs.getFromPTRef(tr);
    SymRef sr = logic.getSymRef(tr);
    if (logic.isBVConcat(sr)) return bbConcat(tr);
    if (logic.isBVConst(sr)) return bbConstant(tr);
    if (logic.isBVNot(sr)) return bbNot(tr);
    if (logic.isBVNeg(sr)) return bbNeg(tr);
    if (logic.isBVAnd(sr)) return bbAnd(tr);
    if (logic.isBVOr(sr)) return bbOr(tr);
    if (logic.isBVAdd(sr)) return bbAdd(tr);
    if (logic.isBVMul(sr)) return bbMul(tr);
    if (logic.isBVUdiv(sr)) return bbUdiv(tr);
    if (logic.isBVUrem(sr)) return bbUrem(tr);
    if (logic.isBVShl(sr)) return bbShl(tr);
    if (logic.isBVLshr(sr)) return bbLshr(tr);
    if (logic.isBVVar(sr)) return bbVar(tr);

    char * name = logic.pp(tr);
    std::string name_s(name);
    free(name);
    throw OsmtInternalException("Unknown bit-vector operation " + name_s);
    // Unreachable
}

BVRef FSBVBitBlaster::bbAdd(PTRef tr) {
    assert(tr != PTRef_Undef);
    assert( logic.getPterm(tr).size() == 2 );

    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names = getBVVars(s_add, logic.getRetSortBitWidth(tr));

    // Allocate new result
    vec<PTRef> result;

    PTRef arg1 = logic.getPterm(tr)[0];
    PTRef arg2 = logic.getPterm(tr)[1];
    BVRef bb_arg1 = bbTerm(arg1);
    BVRef bb_arg2 = bbTerm(arg2);
    assert( bs[bb_arg1].size() == bs[bb_arg2].size() );

    PTRef carry = PTRef_Undef;

    int bw = bs[bb_arg1].size(); // the bit width
    for (int i = 0 ; i < bw; i++) {
        PTRef bit_1 = bs[bb_arg1][i];
        PTRef bit_2 = bs[bb_arg2][i];
        assert(bit_1 != PTRef_Undef);
        assert(bit_2 != PTRef_Undef);

        PTRef xor_1 = logic.mkXor(bit_1, bit_2);
        PTRef and_1 = logic.mkAnd(bit_1, bit_2);

        if (carry != PTRef_Undef) {
            PTRef xor_2 = logic.mkXor(xor_1, carry);
            PTRef and_2 = logic.mkAnd(xor_1, carry);
            carry = logic.mkOr(and_1, and_2);
            result.push(xor_2);
        }
        else {
            carry = and_1;
            result.push(xor_1);
        }
    }

    // Save result and return
    return bs.newBvector(names, result, tr);
}

BVRef FSBVBitBlaster::bbVar(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.isVar(tr));

    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names = getBVVars("bv", logic.getRetSortBitWidth(tr));

    vec<PTRef> result;
    names.copyTo(result);

    BVRef rval = bs.newBvector(names, result, tr);

    return rval;
}

BVRef FSBVBitBlaster::bbMul(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.getPterm(tr).size() == 2 );

    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names = getBVVars(s_mul, logic.getRetSortBitWidth(tr));

    // Allocate new result
    vec<PTRef> result;

    vec<PTRef> acc;
    PTRef arg1 = logic.getPterm(tr)[0];
    PTRef arg2 = logic.getPterm(tr)[1];
    BVRef bb_arg1 = bbTerm(arg1);
    BVRef bb_arg2 = bbTerm(arg2);
    assert(bs[bb_arg1].size() == bs[bb_arg2].size());
    const unsigned size = bs[bb_arg1].size( );
    // Compute term a_{i-1}*b_{j-1} ... a_0*b_0
    for ( unsigned i = 0 ; i < size ; i ++ )
        acc.push(logic.mkAnd(bs[bb_arg2][0], bs[bb_arg1][i]));
    // Multi-arity adder
    for ( unsigned i = 1 ; i < size ; i ++ )
    {
        vec<PTRef> addend;
        // Push trailing 0s
        for ( unsigned j = 0 ; j < i ; j ++ )
            addend.push(logic.getTerm_false());
        // Compute term a_{i-1}*b_i ... a_0*b_i 0 ... 0
        for ( unsigned j = 0 ; j < size - i ; j ++ )
            addend.push(logic.mkAnd(bs[bb_arg2][i], bs[bb_arg1][j]));

        assert(static_cast<unsigned>(addend.size()) == size);
        // Accumulate computed term
        PTRef carry = PTRef_Undef;

        for (unsigned k = 0 ; k < size ; k++)
        {
            PTRef bit_1 = acc[ k ];
            PTRef bit_2 = addend[ k ];
            assert(bit_1 != PTRef_Undef);
            assert(bit_2 != PTRef_Undef);

            PTRef xor_1 = logic.mkXor(bit_1, bit_2);
            PTRef and_1 = logic.mkAnd(bit_1, bit_2 );

            if (carry != PTRef_Undef)
            {
                PTRef xor_2 = logic.mkXor(xor_1, carry);
                PTRef and_2 = logic.mkAnd(xor_1, carry);
                carry = logic.mkOr(and_1, and_2);
                if ( i == size - 1 )
                    result.push(xor_2);
                else
                    acc[k] = xor_2;
            }
            else
            {
                carry = and_1;
                if ( i == size - 1 )
                    result.push(xor_1);
                else
                    acc[k] = xor_1;
            }
        }
    }

    return bs.newBvector(names, result, tr);
}

BVRef FSBVBitBlaster::bbConstant(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.isConstant(tr));

    if (bs.has(tr)) return bs[tr];
    BitWidth_t bw = logic.getRetSortBitWidth(tr);
    // Allocate new result
    vec<PTRef> names = getBVVars("c", bw);

    vec<PTRef> asgns;
    asgns.growTo(bw, logic.getTerm_false());

    if (logic.isTrue(tr))
        asgns[0] = logic.getTerm_true();
    else if (logic.isFalse(tr))
        ; // already ok
    else {
        const std::string value = logic.getSymName(tr);
        assert((value.length()-2) == static_cast<unsigned>(bw));
        for (unsigned int i = 0 ; i < bw; ++i) {
            unsigned int idx = bw-i+1;
            assert(value[idx] == '1' or value[idx] == '0');
            asgns[i] = value[idx] == '1' ? logic.getTerm_true() : logic.getTerm_false();
        }
    }
    // Save result and return
    return bs.newBvector(names, asgns, tr);
}

PTRef FSBVBitBlaster::bbUlt(PTRef tr)
{
    assert(tr != PTRef_Undef);

    // Return previous result if computed
    // TODO: cache results!

    // Allocate new result
    assert(logic.getPterm(tr).size() == 2 );
    PTRef lhs = logic.getPterm(tr)[0];
    PTRef rhs = logic.getPterm(tr)[1];

    // Retrieve arguments' encodings
    BVRef bb_lhs = bbTerm(lhs);
    BVRef bb_rhs = bbTerm(rhs);
    assert(bs[bb_lhs].size() == bs[bb_rhs].size());
    //
    // Produce the result
    //
    PTRef lt_prev = PTRef_Undef;
    for (int i = 0 ; i < bs[bb_lhs].size() ; i ++)
    {
        // Produce ~l[i] & r[i]
        PTRef not_l   = logic.mkNot(bs[bb_lhs][i]);
        PTRef lt_this = logic.mkAnd(not_l, bs[bb_rhs][i]);
        // Produce l[i] <-> r[i]
        PTRef eq_this = logic.mkEq(bs[bb_lhs][i], bs[bb_rhs][i]);
        if (lt_prev != PTRef_Undef)
            lt_prev = logic.mkOr(lt_this, logic.mkAnd(eq_this, lt_prev));
        else
            lt_prev = lt_this;
    }
    return lt_prev;
}