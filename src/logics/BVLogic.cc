/*******************************************************************\
Module: New Logic for BitVector

 *  Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *  Author: Sepideh Asadi <sepideh.a65@gmail.com>
 *  Created on: Jan 16, 2017
\*******************************************************************/

#include "SStore.h"
#include "PtStore.h"
#include "BVLogic.h"
#include "CUFLogic.h"
#include "TreeOps.h"
#include "Global.h"

int         BVLogic::tk_bv_zero  = 0;
int         BVLogic::tk_bv_one   = 1;
const char* BVLogic::tk_bv_neg   = "-";
const char* BVLogic::tk_bv_eq    = "==";
const char* BVLogic::tk_bv_minus = "-";
const char* BVLogic::tk_bv_plus  = "+";
const char* BVLogic::tk_bv_times = "*";
const char* BVLogic::tk_bv_div   = "/";
const char* BVLogic::tk_bv_slt   = "s<";
const char* BVLogic::tk_bv_ult   = "u<";
const char* BVLogic::tk_bv_sleq   = "s<=";
const char* BVLogic::tk_bv_uleq   = "u<=";
const char* BVLogic::tk_bv_sgt    = "s>";
const char* BVLogic::tk_bv_ugt    = "u>";
const char* BVLogic::tk_bv_sgeq   = "s>=";
const char* BVLogic::tk_bv_ugeq   = "u>=";
const char* BVLogic::tk_bv_lshift = "<<";
const char* BVLogic::tk_bv_arshift = "a>>";
const char* BVLogic::tk_bv_lrshift = "l>>";
const char* BVLogic::tk_bv_mod    = "%";
const char* BVLogic::tk_bv_bwand  = "&";
const char* BVLogic::tk_bv_bwor   = "|";
const char* BVLogic::tk_bv_land   = "&&";
const char* BVLogic::tk_bv_lor    = "||";
const char* BVLogic::tk_bv_not    = "!";
const char* BVLogic::tk_bv_bwxor  = "^";
const char* BVLogic::tk_bv_compl  = "~";

const char*  BVLogic::s_sort_bvnum = "BVNum";
//const char*  BVLogic::s_sort_bvstr = "BVStr";

const char* BVLogic::s_uf_extract_base = ".ex";
const char* BVLogic::tk_bv_coll32 = ".coll32";

const int BVLogic::i_default_bitwidth = 32;

BVLogic::BVLogic(int width) :
    CUFLogic()
    , sym_BV_ZERO(SymRef_Undef)
    , sym_BV_ONE(SymRef_Undef)
    , sym_BV_NEG(SymRef_Undef)
    , sym_BV_MINUS(SymRef_Undef)
    , sym_BV_PLUS(SymRef_Undef)
    , sym_BV_TIMES(SymRef_Undef)
    , sym_BV_DIV(SymRef_Undef)
    , sym_BV_EQ(SymRef_Undef)
    , sym_BV_SLEQ(SymRef_Undef)
    , sym_BV_ULEQ(SymRef_Undef)
    , sym_BV_SGEQ(SymRef_Undef)
    , sym_BV_UGEQ(SymRef_Undef)
    , sym_BV_SLT(SymRef_Undef)
    , sym_BV_ULT(SymRef_Undef)
    , sym_BV_SGT(SymRef_Undef)
    , sym_BV_UGT(SymRef_Undef)
    , sym_BV_BWXOR(SymRef_Undef)
    , sym_BV_LSHIFT(SymRef_Undef)
    , sym_BV_LRSHIFT(SymRef_Undef)
    , sym_BV_ARSHIFT(SymRef_Undef)
    , sym_BV_MOD(SymRef_Undef)
    , sym_BV_BWOR(SymRef_Undef)
    , sym_BV_BWAND(SymRef_Undef)
    , sym_BV_LAND(SymRef_Undef)
    , sym_BV_LOR(SymRef_Undef)
    , sym_BV_NOT(SymRef_Undef)
    , sym_BV_COMPL(SymRef_Undef)
    , sym_BV_COLLATE32(SymRef_Undef)

    , sort_BVNUM(SRef_Undef)
    , term_BV_ZERO(PTRef_Undef)
    , term_BV_ONE(PTRef_Undef)
    , bitwidth(width)
{
    char* msg;
    sort_BVNUM = declareSort(s_sort_bvnum, &msg);

    vec<SRef> params;
    term_BV_ZERO = mkBVConst(tk_bv_zero);
    sym_BV_ZERO  = getSymRef(term_BV_ZERO);
    term_BV_ONE  = mkBVConst(tk_bv_one);
    sym_BV_ONE   = getSymRef(term_BV_ONE);

    params.push(sort_BVNUM);

    // Unary
    sym_BV_NEG    = declareFun(tk_bv_neg, sort_BVNUM, params, &msg, true);
    sym_BV_COMPL  = declareFun(tk_bv_compl, sort_BVNUM, params, &msg, true);
    sym_BV_NOT = declareFun(tk_bv_not, sort_BVNUM, params, &msg, true);

    params.push(sort_BVNUM);

    // Binary
    sym_BV_MINUS = declareFun(tk_bv_neg, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_MINUS].setLeftAssoc();

    sym_BV_EQ    = declareFun(tk_bv_eq, sort_BVNUM, params, &msg, true);
    equalities.insert(sym_BV_EQ, true);
    sym_store[sym_BV_EQ].setNoScoping();
    sym_store[sym_BV_EQ].setCommutes();
    sym_store[sym_BV_EQ].setLeftAssoc();

    sym_BV_PLUS  = declareFun(tk_bv_plus, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_PLUS].setNoScoping();
    sym_store[sym_BV_PLUS].setCommutes();
    sym_store[sym_BV_PLUS].setLeftAssoc();

    sym_BV_TIMES = declareFun(tk_bv_times, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_TIMES].setNoScoping();
    sym_store[sym_BV_TIMES].setLeftAssoc();
    sym_store[sym_BV_TIMES].setCommutes();

    sym_BV_DIV   = declareFun(tk_bv_div, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_DIV].setNoScoping();
    sym_store[sym_BV_DIV].setLeftAssoc();

    sym_BV_SLEQ  = declareFun(tk_bv_sleq, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_SLEQ].setNoScoping();
    sym_store[sym_BV_SLEQ].setChainable();

    sym_BV_ULEQ  = declareFun(tk_bv_uleq, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_ULEQ].setNoScoping();
    sym_store[sym_BV_ULEQ].setChainable();

    sym_BV_SLT  = declareFun(tk_bv_slt, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_SLT].setNoScoping();
    sym_store[sym_BV_SLT].setChainable();

    sym_BV_ULT  = declareFun(tk_bv_ult, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_ULT].setNoScoping();
    sym_store[sym_BV_ULT].setChainable();

    sym_BV_UGEQ = declareFun(tk_bv_ugeq, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_UGEQ].setNoScoping();
    sym_store[sym_BV_UGEQ].setChainable();

    sym_BV_SGEQ = declareFun(tk_bv_sgeq, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_SGEQ].setNoScoping();
    sym_store[sym_BV_SGEQ].setChainable();

    sym_BV_SGT  = declareFun(tk_bv_sgt, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_SGT].setNoScoping();
    sym_store[sym_BV_SGT].setChainable();

    sym_BV_UGT   = declareFun(tk_bv_ugt, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_UGT].setNoScoping();
    sym_store[sym_BV_UGT].setChainable();

    sym_BV_LAND   = declareFun(tk_bv_land, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_LAND].setCommutes();

    sym_BV_LOR    = declareFun(tk_bv_lor, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_LOR].setCommutes();

    sym_BV_LSHIFT = declareFun(tk_bv_lshift, sort_BVNUM, params, &msg, true);

    sym_BV_ARSHIFT = declareFun(tk_bv_arshift, sort_BVNUM, params, &msg, true);
    sym_BV_LRSHIFT = declareFun(tk_bv_lrshift, sort_BVNUM, params, &msg, true);

    sym_BV_MOD    = declareFun(tk_bv_mod, sort_BVNUM, params, &msg, true);

    sym_BV_BWAND  = declareFun(tk_bv_bwand, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_BWAND].setCommutes();

    sym_BV_BWOR   = declareFun(tk_bv_bwor, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_BWOR].setCommutes();

    sym_BV_BWXOR  = declareFun(tk_bv_bwxor, sort_BVNUM, params, &msg, true);
    sym_store[sym_BV_BWXOR].setCommutes();

    declareFun(tk_bv_neg, sort_BVNUM, params, &msg, true);

    vec<SRef> coll_params;
    for (int i = 0; i < 32; i++)
        coll_params.push(getSort_bool());
    sym_BV_COLLATE32 = declareFun(tk_bv_coll32, sort_CUFNUM, coll_params, &msg, true);

    for (int i = 0; i < 32; i++) {
        std::string sym_name {s_uf_extract_base};
        sym_name += std::to_string(i);
        declareFun(sym_name.c_str(), getSort_bool(), {sort_CUFNUM}, &msg, true);
    }
}

BVLogic::~BVLogic()
{}

PTRef
BVLogic::mkBVEq(PTRef a1, PTRef a2)
{
    assert(hasSortBVNUM(a1));
    assert(hasSortBVNUM(a2));

    if (isConstant(a1) && isConstant(a2))
        return (a1 == a2) ? getTerm_BVOne() : getTerm_BVZero();
    if (a1 == a2) return getTerm_BVOne();
    if (a1 == mkBVNot(a2)) return getTerm_BVZero();
    return mkFun(sym_BV_EQ, {a1,a2});
}

PTRef
BVLogic::mkBVNeg(PTRef tr)
{
    assert(hasSortBVNUM(tr));
    if (isBVNeg(tr)) return getPterm(tr)[0];
    if (isConstant(tr)) {
        int v = getBVNUMConst(tr);
        v = -v;
        PTRef nterm = mkBVConst(v);
        return nterm;
    }
    vec<PTRef> arg;
    arg.push(getTerm_BVZero());
    arg.push(tr);
    return mkBVMinus(arg);
}

PTRef
BVLogic::mkBVMinus(const vec<PTRef>& args_in)
{
    for (int i = 0; i < args_in.size(); i++)
        assert(hasSortBVNUM(args_in[i]));

    vec<PTRef> args;
    args_in.copyTo(args);
    if (args.size() == 1)
        return mkBVNeg(args[0]);

    assert(args.size() == 2);
    PTRef mo = mkBVConst(-1);
    PTRef fact = mkBVTimes(mo, args[1]);
    args[1] = fact;
    return mkBVPlus(args[0], args[1]);
}

PTRef
BVLogic::mkBVPlus(const PTRef arg1, const PTRef arg2)
{

    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));

    PTRef tr = mkFun(sym_BV_PLUS, {arg1, arg2});
//    sum_args[0] = arg2;
//    sum_args[1] = arg1;
//    PTRef tr_comm = mkFun(sym_BV_PLUS, sum_args, msg);
//    PTRef tr_comm_eq = mkEq(tr, tr_comm);
//    if (!comm_eqs.has(tr_comm_eq))
//        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}


PTRef
BVLogic::mkBVTimes(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));

    PTRef tr = mkFun(sym_BV_TIMES, {arg1, arg2});
//    times_args[0] = arg2;
//    times_args[1] = arg1;
//    PTRef tr_comm = mkFun(sym_BV_TIMES, times_args, msg);
//    PTRef tr_comm_eq = mkEq(tr, tr_comm);
//    if (!comm_eqs.has(tr_comm_eq))
//        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}

PTRef
BVLogic::mkBVDiv(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));

    PTRef tr = mkFun(sym_BV_DIV, {arg1, arg2});
    return tr;
}

PTRef
BVLogic::mkBVUgeq(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));
    return mkBVUleq(arg2, arg1);
}


PTRef
BVLogic::mkBVSgeq(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));
    return mkBVSleq(arg2, arg1);
}

PTRef
BVLogic::mkBVUgt(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));
    return mkBVUlt(arg2, arg1);
}


PTRef
BVLogic::mkBVSgt(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));
    return mkBVSlt(arg2, arg1);
}

PTRef
BVLogic::mkBVSleq(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));

    if (isBVNUMConst(arg1) && isBVNUMConst(arg2)) {
        int c1 = (int)getBVNUMConst(arg1);
        int c2 = (int)getBVNUMConst(arg2);
        if (c1 <= c2)
            return term_BV_ONE;
        else
            return term_BV_ZERO;
    }
    return mkBVNot(mkBVSgt(arg1, arg2));
}

PTRef
BVLogic::mkBVUleq(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));

    if (isBVNUMConst(arg1) && isBVNUMConst(arg2)) {
        unsigned c1 = (unsigned)getBVNUMConst(arg1);
        unsigned c2 = (unsigned)getBVNUMConst(arg2);
        if (c1 <= c2)
            return term_BV_ONE;
        else
            return term_BV_ZERO;
    }
    PTRef tr = mkFun(sym_BV_ULEQ, {arg1, arg2});
    return tr;
}

PTRef
BVLogic::mkBVUlt(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));
    return mkBVNeg(mkBVUgeq(arg1, arg2));
}

PTRef
BVLogic::mkBVSlt(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));

    if (isBVNUMConst(arg1) && isBVNUMConst(arg2)) {
        int c1 = (int)getBVNUMConst(arg1);
        int c2 = (int)getBVNUMConst(arg2);
        if (c1 < c2)
            return term_BV_ONE;
        else
            return term_BV_ZERO;
    }
    PTRef tr = mkFun(sym_BV_SLT, {arg1, arg2});
    return tr;
}


PTRef BVLogic::mkBVLshift(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));
    if (isBVNUMConst(arg2) && getBVNUMConst(arg2) == 0)
        return arg1;
    return mkFun(sym_BV_LSHIFT, {arg1, arg2});
}

PTRef BVLogic::mkBVLRshift(const PTRef arg1, const PTRef arg2)
{
    if (isBVNUMConst(arg2) && getBVNUMConst(arg2) == 0)
        return arg1;
    return mkFun(sym_BV_LRSHIFT, {arg1, arg2});
}

PTRef BVLogic::mkBVARshift(const PTRef arg1, const PTRef arg2)
{
    if (isBVNUMConst(arg2) && getBVNUMConst(arg2) == 0)
        return arg1;
    return mkFun(sym_BV_ARSHIFT, {arg1, arg2});
}


PTRef BVLogic::mkBVMod(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));

    if (isBVNUMConst(arg2) && getBVNUMConst(arg2) == 1)
        return getTerm_BVZero();
    // if b > 0, then 0 <= a % b < b
    // if b < 0, then b < a % b <= 0
    return mkFun(sym_BV_MOD, {arg1, arg2});
}

PTRef BVLogic::mkBVBwAnd(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));
    return mkFun(sym_BV_BWAND, {arg1, arg2});
}

PTRef BVLogic::mkBVBwOr(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));
    return mkFun(sym_BV_BWOR, {arg1, arg2});
}

PTRef BVLogic::mkBVLand(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));
    PTRef tr = mkFun(sym_BV_LAND, {arg1, arg2});
    return tr;
}

PTRef BVLogic::mkBVLor(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));
    PTRef tr = mkFun(sym_BV_LOR, {arg1, arg2});
    return tr;
}

PTRef BVLogic::mkBVNot(const PTRef arg)
{
    assert(hasSortBVNUM(arg));
    if (isBVNot(arg))
        return getPterm(arg)[0];
    else if (isConstant(arg) && (arg != term_BV_ZERO))
        return term_BV_ZERO;
    else if (arg == term_BV_ZERO)
        return term_BV_ONE;
    PTRef tr = mkFun(sym_BV_NOT, {arg});
    return tr;
}

PTRef BVLogic::mkBVBwXor(const PTRef arg1, const PTRef arg2)
{
    assert(hasSortBVNUM(arg1));
    assert(hasSortBVNUM(arg2));
    return mkFun(sym_BV_BWXOR, {arg1, arg2});
}

PTRef BVLogic::mkBVCompl(const PTRef arg1)
{
    assert(hasSortBVNUM(arg1));
    PTRef tr = mkFun(sym_BV_COMPL, {arg1});
//    PTRef neq = mkBVNeq(tr, arg1);
//    if (!compl_diseqs.has(neq))
//        compl_diseqs.insert(neq, true);
    return tr;
}

PTRef BVLogic::mkBVNeq(const PTRef a1, const PTRef a2)
{
    assert(hasSortBVNUM(a1));
    assert(hasSortBVNUM(a2));
    vec<PTRef> args;
    args.push(a1);
    args.push(a2);
    return mkBVNot(mkBVEq(args));
}

const int BVLogic::getBVNUMConst(PTRef tr) const
{
    return atoi(getSymName(tr));
}
