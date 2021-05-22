/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2017 Antti Hyvarinen

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include "SStore.h"
#include "PtStore.h"
#include "CUFLogic.h"
#include "TreeOps.h"
#include "Global.h"

int CUFLogic::tk_cuf_zero  = 0;
int CUFLogic::tk_cuf_one   = 1;
const char* CUFLogic::tk_cuf_neg   = "-";
const char* CUFLogic::tk_cuf_minus = "-";
const char* CUFLogic::tk_cuf_plus  = "+";
const char* CUFLogic::tk_cuf_times = "*";
const char* CUFLogic::tk_cuf_div   = "/";
const char* CUFLogic::tk_cuf_lt    = "<";
const char* CUFLogic::tk_cuf_leq   = "<=";
const char* CUFLogic::tk_cuf_gt    = ">";
const char* CUFLogic::tk_cuf_geq   = ">=";

const char* CUFLogic::tk_cuf_lshift = "<<";
const char* CUFLogic::tk_cuf_lrshift = "l>>";
const char* CUFLogic::tk_cuf_arshift = "a>>";
const char* CUFLogic::tk_cuf_mod    = "%";
const char* CUFLogic::tk_cuf_bwand  = "&";
const char* CUFLogic::tk_cuf_bwor   = "|";
const char* CUFLogic::tk_cuf_inc    = "++";
const char* CUFLogic::tk_cuf_dec    = "--";
const char* CUFLogic::tk_cuf_neq    = "!=";
const char* CUFLogic::tk_cuf_land   = "&&";
const char* CUFLogic::tk_cuf_lor    = "||";
const char* CUFLogic::tk_cuf_not    = "!";
const char* CUFLogic::tk_cuf_bwxor  = "^";
const char* CUFLogic::tk_cuf_compl  = "~";
const char* CUFLogic::tk_cuf_sizeof = "sizeof";
const char* CUFLogic::tk_cuf_addrof = "&";
const char* CUFLogic::tk_cuf_ptr    = "*";
const char* CUFLogic::tk_cuf_cond   = "?";

const char*  CUFLogic::s_sort_cufnum = "CUFNum";
const char*  CUFLogic::s_sort_cufstr = "CUFStr";

CUFLogic::CUFLogic() :
    Logic()
    , sym_CUF_ZERO(SymRef_Undef)
    , sym_CUF_ONE(SymRef_Undef)
    , sym_CUF_NEG(SymRef_Undef)
    , sym_CUF_MINUS(SymRef_Undef)
    , sym_CUF_PLUS(SymRef_Undef)
    , sym_CUF_TIMES(SymRef_Undef)
    , sym_CUF_DIV(SymRef_Undef)
//    , sym_CUF_EQ(SymRef_Undef)
    , sym_CUF_LEQ(SymRef_Undef)
    , sym_CUF_LT(SymRef_Undef)
    , sym_CUF_GEQ(SymRef_Undef)
    , sym_CUF_GT(SymRef_Undef)
    , sym_CUF_LSHIFT(SymRef_Undef)
    , sym_CUF_LRSHIFT(SymRef_Undef)
    , sym_CUF_ARSHIFT(SymRef_Undef)
    , sym_CUF_MOD(SymRef_Undef)
    , sym_CUF_BWAND(SymRef_Undef)
    , sym_CUF_BWOR(SymRef_Undef)
    , sym_CUF_INC(SymRef_Undef)
    , sym_CUF_DEC(SymRef_Undef)
    , sym_CUF_NEQ(SymRef_Undef)
    , sym_CUF_LAND(SymRef_Undef)
    , sym_CUF_LOR(SymRef_Undef)
//    , sym_CUF_NOT(SymRef_Undef)
    , sym_CUF_BWXOR(SymRef_Undef)
    , sym_CUF_COMPL(SymRef_Undef)
    , sym_CUF_SIZEOF(SymRef_Undef)
    , sym_CUF_ADDROF(SymRef_Undef)
    , sym_CUF_PTR(SymRef_Undef)
//    , sym_CUF_COND(SymRef_Undef)

    , sort_CUFNUM(SRef_Undef)
    , sort_CUFSTR(SRef_Undef)

    , term_CUF_ZERO(PTRef_Undef)
    , term_CUF_ONE(PTRef_Undef)
{
    char* msg;
    sort_CUFNUM = declareSort(s_sort_cufnum, &msg);

    vec<SRef> params;
    term_CUF_ZERO = mkCUFConst(tk_cuf_zero);
    sym_CUF_ZERO  = getSymRef(term_CUF_ZERO);
    term_CUF_ONE  = mkCUFConst(tk_cuf_one);
    sym_CUF_ONE   = getSymRef(term_CUF_ONE);

    params.push(sort_CUFNUM);

    // Unary
    sym_CUF_NEG    = declareFun(tk_cuf_neg, sort_CUFNUM, params, &msg, true);
    sym_CUF_INC    = declareFun(tk_cuf_inc, sort_CUFNUM, params, &msg, true);
    sym_CUF_DEC    = declareFun(tk_cuf_dec, sort_CUFNUM, params, &msg, true);
    sym_CUF_COMPL  = declareFun(tk_cuf_compl, sort_CUFNUM, params, &msg, true);
    sym_CUF_SIZEOF = declareFun(tk_cuf_sizeof, sort_CUFNUM, params, &msg, true);
    sym_CUF_ADDROF = declareFun(tk_cuf_addrof, sort_CUFNUM, params, &msg, true);
    sym_CUF_PTR    = declareFun(tk_cuf_ptr, sort_CUFNUM, params, &msg, true);

    params.push(sort_CUFNUM);
    // Binary
    sym_CUF_MINUS = declareFun(tk_cuf_neg, sort_CUFNUM, params, &msg, true);
    sym_store[sym_CUF_MINUS].setLeftAssoc();

    sym_CUF_PLUS  = declareFun(tk_cuf_plus, sort_CUFNUM, params, &msg, true);
    sym_store[sym_CUF_PLUS].setNoScoping();
//    sym_store[sym_CUF_PLUS].setCommutes();
    sym_store[sym_CUF_PLUS].setLeftAssoc();

    sym_CUF_TIMES = declareFun(tk_cuf_times, sort_CUFNUM, params, &msg, true);
    sym_store[sym_CUF_TIMES].setNoScoping();
    sym_store[sym_CUF_TIMES].setLeftAssoc();
//    sym_store[sym_CUF_TIMES].setCommutes();

    sym_CUF_DIV   = declareFun(tk_cuf_div, sort_CUFNUM, params, &msg, true);
    sym_store[sym_CUF_DIV].setNoScoping();
    sym_store[sym_CUF_DIV].setLeftAssoc();

    sym_CUF_LEQ  = declareFun(tk_cuf_leq, sort_BOOL, params, &msg, true);
    sym_store[sym_CUF_LEQ].setNoScoping();
    sym_store[sym_CUF_LEQ].setChainable();

    sym_CUF_LT   = declareFun(tk_cuf_lt, sort_BOOL, params, &msg, true);
    sym_store[sym_CUF_LT].setNoScoping();
    sym_store[sym_CUF_LT].setChainable();

    sym_CUF_GEQ  = declareFun(tk_cuf_geq, sort_BOOL, params, &msg, true);
    sym_store[sym_CUF_GEQ].setNoScoping();
    sym_store[sym_CUF_GEQ].setChainable();

    sym_CUF_GT   = declareFun(tk_cuf_gt, sort_BOOL, params, &msg, true);
    sym_store[sym_CUF_GEQ].setNoScoping();
    sym_store[sym_CUF_GEQ].setChainable();

    sym_CUF_NEQ    = declareFun(tk_cuf_neq, sort_BOOL, params, &msg, true);
    sym_store[sym_CUF_NEQ].setCommutes();

    sym_CUF_LAND   = declareFun(tk_cuf_land, sort_BOOL, params, &msg, true);
//    sym_store[sym_CUF_LAND].setCommutes();

    sym_CUF_LOR    = declareFun(tk_cuf_lor, sort_BOOL, params, &msg, true);
//    sym_store[sym_CUF_LOR].setCommutes();

    sym_CUF_LSHIFT = declareFun(tk_cuf_lshift, sort_CUFNUM, params, &msg, true);
    sym_CUF_LRSHIFT = declareFun(tk_cuf_lrshift, sort_CUFNUM, params, &msg, true);
    sym_CUF_ARSHIFT = declareFun(tk_cuf_arshift, sort_CUFNUM, params, &msg, true);

    sym_CUF_MOD    = declareFun(tk_cuf_mod, sort_CUFNUM, params, &msg, true);
    sym_CUF_BWAND  = declareFun(tk_cuf_bwand, sort_CUFNUM, params, &msg, true);
//    sym_store[sym_CUF_BWAND].setCommutes();

    sym_CUF_BWOR   = declareFun(tk_cuf_bwor, sort_CUFNUM, params, &msg, true);
//    sym_store[sym_CUF_BWOR].setCommutes();
    sym_CUF_BWXOR  = declareFun(tk_cuf_bwxor, sort_CUFNUM, params, &msg, true);
}

CUFLogic::~CUFLogic()
{}

//PTRef
//CUFLogic::insertTerm(SymRef sym, vec<PTRef>& terms, char **msg)
//{
//    assert(false);
//    return PTRef_Undef;
//}

PTRef
CUFLogic::mkCUFNeg(PTRef tr, char** msg)
{
    if (isCUFNeg(tr)) return getPterm(tr)[0];
    if (isCUFPlus(tr)) {
        vec<PTRef> args;
        assert(getPterm(tr).size() == 2);
        PTRef arg1 = mkCUFNeg(getPterm(tr)[0]);
        PTRef arg2 = mkCUFNeg(getPterm(tr)[1]);
        PTRef tr_n = mkCUFPlus(arg1, arg2, msg);
        assert(tr_n != PTRef_Undef);
        return tr_n;
    }
    if (isConstant(tr)) {
        int v = getCUFNUMConst(tr);
        v = -v;
        PTRef nterm = mkCUFConst(v);
        SymRef s = getPterm(nterm).symb();
        vec<PTRef> args;
        return mkFun(s, args);
    }
    PTRef mo = mkCUFConst(-1);
    return mkCUFTimes(mo, tr);
}

PTRef
CUFLogic::mkCUFMinus(const vec<PTRef>& args_in, char** msg)
{
    vec<PTRef> args;
    args_in.copyTo(args);
    if (args.size() == 1) {
        PTRef ret = mkCUFNeg(args[0], msg);
        return ret;
    }
    else {
        assert(args.size() == 2);
        PTRef mo = mkCUFConst(-1);
        vec<PTRef> tmp;
        PTRef fact = mkCUFTimes(mo, args[1], msg);
        args[1] = fact;
        return mkCUFPlus(args[0], args[1]);
    }
}

PTRef
CUFLogic::mkCUFPlus(const PTRef arg1, const PTRef arg2, char** msg)
{
    vec<PTRef> sum_args;
    sum_args.push(arg1);
    sum_args.push(arg2);
    PTRef tr = mkFun(sym_CUF_PLUS, sum_args);
    sum_args[0] = arg2;
    sum_args[1] = arg1;
    PTRef tr_comm = mkFun(sym_CUF_PLUS, sum_args);
    PTRef tr_comm_eq = mkEq(tr, tr_comm);
    if (!comm_eqs.has(tr_comm_eq))
        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}

// We need this since CUF wants to take care of commutativity on its own
//PTRef
//CUFLogic::insertTermHash(SymRef sym, const vec<PTRef>& terms_in)
//{
//    vec<PTRef> terms;
//    terms_in.copyTo(terms);
//    PTRef res = PTRef_Undef;
//    char **msg;
//    if (terms.size() == 0) {
//        if (term_store.hasCtermKey(sym)) //cterm_map.contains(sym))
//            res = term_store.getFromCtermMap(sym); //cterm_map[sym];
//        else {
//            res = term_store.newTerm(sym, terms);
//            term_store.addToCtermMap(sym, res); //cterm_map.insert(sym, res);
//        }
//    }
//    else if (!isBooleanOperator(sym)) {
//        if (!sym_store[sym].left_assoc() &&
//            !sym_store[sym].right_assoc() &&
//            !sym_store[sym].chainable() &&
//            !sym_store[sym].pairwise() &&
//            sym_store[sym].nargs() != terms.size_())
//        {
//            *msg = (char*)malloc(strlen(e_argnum_mismatch)+1);
//            strcpy(*msg, e_argnum_mismatch);
//            return PTRef_Undef;
//        }
//        PTLKey k;
//        k.sym = sym;
//        terms.copyTo(k.args);
//        if (term_store.hasCplxKey(k))
//            res = term_store.getFromCplxMap(k);
//        else {
//            res = term_store.newTerm(sym, terms);
//            term_store.addToCplxMap(k, res);
//        }
//    }
//    else {
//        // Boolean operator
//        PTLKey k;
//        k.sym = sym;
//        terms.copyTo(k.args);
//        if (term_store.hasBoolKey(k)) {
//            res = term_store.getFromBoolMap(k); //bool_map[k];
//#ifdef SIMPLIFY_DEBUG
//            char* ts = printTerm(res);
//            cerr << "duplicate: " << ts << endl;
//            ::free(ts);
//#endif
//        }
//        else {
//            res = term_store.newTerm(sym, terms);
//            term_store.addToBoolMap(k, res); //bool_map.insert(k, res);
//#ifdef SIMPLIFY_DEBUG
//            char* ts = printTerm(res);
//            cerr << "new: " << ts << endl;
//            ::free(ts);
//#endif
//        }
//    }
//    return res;
//}


PTRef
CUFLogic::mkCUFTimes(const PTRef arg1, const PTRef arg2, char** msg)
{
    vec<PTRef> times_args;
    times_args.push(arg1);
    times_args.push(arg2);

    PTRef tr = mkFun(sym_CUF_TIMES, times_args);
    times_args[0] = arg2;
    times_args[1] = arg1;
    PTRef tr_comm = mkFun(sym_CUF_TIMES, times_args);
    PTRef tr_comm_eq = mkEq(tr, tr_comm);
    if (!comm_eqs.has(tr_comm_eq))
        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}

PTRef
CUFLogic::mkCUFDiv(const PTRef arg1, const PTRef arg2)
{
    vec<PTRef> div_args;
    div_args.push(arg1);
    div_args.push(arg2);
    PTRef tr = mkFun(sym_CUF_DIV, div_args);
    return tr;
}

PTRef
CUFLogic::mkCUFGeq(const PTRef arg1, const PTRef arg2, char** msg)
{
    return mkCUFLeq(arg2, arg1, msg);
}

PTRef
CUFLogic::mkCUFLeq(const PTRef arg1, const PTRef arg2, char** msg)
{
    if (isCUFNUMConst(arg1) && isCUFNUMConst(arg2)) {
        int c1 = getCUFNUMConst(arg1);
        int c2 = getCUFNUMConst(arg2);
        if (c1 <= c2)
            return getTerm_true();
        else
            return getTerm_false();
    }
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    PTRef leq_tr = mkFun(sym_CUF_LEQ, args);
    return mkOr(leq_tr, mkEq(arg1, arg2));
}

PTRef
CUFLogic::mkCUFGt(const PTRef arg1, const PTRef arg2, char** msg)
{
    if (isCUFNUMConst(arg1) && isCUFNUMConst(arg2)) {
        int c1 = getCUFNUMConst(arg1);
        int c2 = getCUFNUMConst(arg2);
        if (c1 > c2)
            return getTerm_true();
        else
            return getTerm_false();
    }
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    PTRef tr = mkFun(sym_CUF_GT, args);
    // a>b -> a != b
    PTRef tr_eq = mkEq(arg1, arg2);
    PTRef n_tr_eq = mkCUFNot(tr_eq);
    PTRef tr_impl = mkImpl(n_tr_eq, n_tr_eq);
    if (!diseq_eqs.has(tr_impl))
        diseq_eqs.insert(tr_impl, true);
    return tr;
}

PTRef CUFLogic::mkCUFLt(const PTRef arg1, const PTRef arg2, char** msg)
{
    return mkCUFGt(arg2, arg1, msg);
}

PTRef CUFLogic::mkCUFLshift(const PTRef arg1, const PTRef arg2)
{
    if (isCUFNUMConst(arg2) && getCUFNUMConst(arg2) == 0)
        return arg1;
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    return mkFun(sym_CUF_LSHIFT, args);
}

PTRef CUFLogic::mkCUFLRshift(const PTRef arg1, const PTRef arg2)
{
    if (isCUFNUMConst(arg2) && getCUFNUMConst(arg2) == 0)
        return arg1;
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    return mkFun(sym_CUF_LRSHIFT, args);
}

PTRef CUFLogic::mkCUFARshift(const PTRef arg1, const PTRef arg2)
{
    if (isCUFNUMConst(arg2) && getCUFNUMConst(arg2) == 0)
        return arg1;
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    return mkFun(sym_CUF_ARSHIFT, args);
}

PTRef CUFLogic::mkCUFMod(const PTRef arg1, const PTRef arg2)
{
    if (isCUFNUMConst(arg2) && getCUFNUMConst(arg2) == 1)
        return getTerm_CUFZero();
    // if b > 0, then 0 <= a % b < b
    // if b < 0, then b < a % b <= 0
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    return mkFun(sym_CUF_MOD, args);
}

PTRef CUFLogic::mkCUFBwAnd(const PTRef arg1, const PTRef arg2)
{
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    PTRef tr = mkFun(sym_CUF_BWAND, args);
    args[0] = arg2;
    args[1] = arg1;
    PTRef tr_comm = mkFun(sym_CUF_BWAND, args);
    PTRef tr_comm_eq = mkEq(tr, tr_comm);
    if (!comm_eqs.has(tr_comm_eq))
        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}

PTRef CUFLogic::mkCUFBwOr(const PTRef arg1, const PTRef arg2)
{
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    PTRef tr = mkFun(sym_CUF_BWOR, args);
    args[0] = arg2;
    args[1] = arg1;
    PTRef tr_comm = mkFun(sym_CUF_BWOR, args);
    PTRef tr_comm_eq = mkEq(tr, tr_comm);
    if (!comm_eqs.has(tr_comm_eq))
        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}

PTRef CUFLogic::mkCUFInc(const PTRef arg1)
{
    vec<PTRef> args;
    args.push(arg1);
    PTRef tr = mkFun(sym_CUF_INC, args);
    PTRef neq = mkCUFNeq(arg1, tr);
    if (!inc_diseqs.has(neq))
        inc_diseqs.insert(neq, true);
    return tr;
}

PTRef CUFLogic::mkCUFDec(const PTRef arg1)
{
    vec<PTRef> args;
    args.push(arg1);
    PTRef tr = mkFun(sym_CUF_DEC, args);
    PTRef neq = mkCUFNeq(arg1, tr);
    if (!inc_diseqs.has(neq))
        inc_diseqs.insert(neq, true);
    return tr;
}

PTRef CUFLogic::mkCUFLand(const PTRef arg1, const PTRef arg2)
{
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    PTRef tr = mkFun(sym_CUF_LAND, args);
    return tr;
}

PTRef CUFLogic::mkCUFLor(const PTRef arg1, const PTRef arg2)
{
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    PTRef tr = mkFun(sym_CUF_LOR, args);
    return tr;
}

PTRef CUFLogic::mkCUFNot(const PTRef arg)
{
    return Logic::mkNot(arg);
}

PTRef CUFLogic::mkCUFBwXor(const PTRef arg1, const PTRef arg2)
{
    vec<PTRef> args;
    args.push(arg1);
    args.push(arg2);
    PTRef tr = mkFun(sym_CUF_BWXOR, args);
    args[0] = arg2;
    args[1] = arg1;
    PTRef tr_comm = mkFun(sym_CUF_BWXOR, args);
    PTRef tr_comm_eq = mkEq(tr, tr_comm);
    if (!comm_eqs.has(tr_comm_eq))
        comm_eqs.insert(tr_comm_eq, true);
    return tr;
}

PTRef CUFLogic::mkCUFCompl(const PTRef arg1)
{
    vec<PTRef> args;
    args.push(arg1);
    PTRef tr = mkFun(sym_CUF_COMPL, args);
    PTRef neq = mkCUFNeq(tr, arg1);
    if (!compl_diseqs.has(neq))
        compl_diseqs.insert(neq, true);
    return tr;
}

PTRef CUFLogic::mkCUFSizeof(const PTRef arg)
{
    vec<PTRef> args;
    args.push(arg);
    return mkFun(sym_CUF_SIZEOF, args);
}

PTRef CUFLogic::mkCUFAddrof(const PTRef arg)
{
    vec<PTRef> args;
    args.push(arg);
    return mkFun(sym_CUF_SIZEOF, args);
}


PTRef CUFLogic::mkCUFPtr(const PTRef arg)
{
    vec<PTRef> args;
    args.push(arg);
    return mkFun(sym_CUF_PTR, args);
}

PTRef CUFLogic::mkCUFCond(const PTRef cond, PTRef i_arg, PTRef e_arg)
{
    return mkIte(cond, i_arg, e_arg);
}

PTRef CUFLogic::mkCUFNeq(const PTRef a1, const PTRef a2)
{
    return Logic::mkNot(Logic::mkEq(a1, a2));
}

const int CUFLogic::getCUFNUMConst(PTRef tr) const
{
    return atoi(getSymName(tr));
}

PTRef CUFLogic::conjoinExtras(PTRef root)
{
    PTRef root_out = root;
    root_out = mkAnd(root_out, mkAnd(comm_eqs.getKeys()));
    root_out = mkAnd(root_out, mkAnd(diseq_eqs.getKeys()));
    root_out = mkAnd(root_out, mkAnd(diseq_split.getKeys()));
    root_out = mkAnd(root_out, mkAnd(mod_ineqs.getKeys()));
    root_out = mkAnd(root_out, mkAnd(inc_diseqs.getKeys()));
    root_out = mkAnd(root_out, mkAnd(compl_diseqs.getKeys()));
    return root_out;
}
