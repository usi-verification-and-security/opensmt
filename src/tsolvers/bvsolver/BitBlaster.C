/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT2 -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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

/*
 * FIXME: MANY LINES ARE DISABLED AS THEY HAVE TO BE
 *        FIXED WRT SMTLIB2
 */

#include "BitBlaster.h"
#include "BVStore.h"

const char* BitBlaster::s_bbEq          = ".bbEq";
const char* BitBlaster::s_bbAnd         = ".bbAnd";
const char* BitBlaster::s_bbBvsle       = ".bbBvsle";
const char* BitBlaster::s_bbBvule       = ".bbBvule";
const char* BitBlaster::s_bbConcat      = ".bbConcat";
const char* BitBlaster::s_bbExtract     = ".bbExtract";
const char* BitBlaster::s_bbBvand       = ".bbBvand";
const char* BitBlaster::s_bbBvland      = ".bbBvland";
const char* BitBlaster::s_bbBvor        = ".bbBvor";
const char* BitBlaster::s_bbBvlor       = ".bbBvlor";
const char* BitBlaster::s_bbBvxor       = ".bbBvxor";
const char* BitBlaster::s_bbBvcompl     = ".bbBvcompl";
const char* BitBlaster::s_bbBvlnot      = ".bbBvlnot";
const char* BitBlaster::s_bbBvadd       = ".bbBvadd";
const char* BitBlaster::s_bbBvmul       = ".bbBvmul";
const char* BitBlaster::s_bbBvudiv      = ".bbBvudiv";
const char* BitBlaster::s_bbBvurem      = ".bbBvurem";
const char* BitBlaster::s_bbSignExtend  = ".bbSignExtend";
const char* BitBlaster::s_bbVar         = ".bbVar";
const char* BitBlaster::s_bbConstant    = ".bbConstant";
const char* BitBlaster::s_bbDistinct    = ".bbDistinct";

BitBlaster::BitBlaster ( const SolverId i
                       , SMTConfig & c
                       , MainSolver& mainSolver
                       , BVLogic& bvlogic
                       , vec<PtAsgn> & ex
                       , vec<DedElem> & d
                       , vec<PTRef> & s )
    : config      (c)
    , mainSolver  (mainSolver)
    , logic       (bvlogic)
    , thandler    (mainSolver.getTHandler())
    , solverP     (mainSolver.getSMTSolver())
    , explanation (ex)
    , deductions  (d)
    , suggestions (s)
    , has_model   (false)
    , bitwidth    (logic.getBitWidth())
{ }

BitBlaster::~BitBlaster ()
{
    cleanGarbage( );
}

BVRef
BitBlaster::updateCache(PTRef tr)
{
    // Return previous result if computed
    if (bs.has(tr))
        return bs.getFromPTRef(tr);
    return BVRef_Undef;
}

//=============================================================================
// Public Interface Routines

lbool
BitBlaster::inform (PTRef tr)
{
    BVRef result = bbTerm( tr );

    char* msg;

    vec<PTRef> bv;
    bs.copyAsgnTo(result, bv);
    PTRef tr_out = logic.mkImpl(bs[result].getActVar(), logic.mkAnd(bv));
    sstat status = mainSolver.insertFormula(tr_out, &msg);
    if (status == s_True)
        return l_True;
    else if (status == s_False)
        return l_False;
    else
        return l_Undef;
}

lbool
BitBlaster::insert(PTRef tr, BVRef& out)
{
    char* msg;
    out = bbTerm(tr);

    PTRef last_bit = logic.mkEq(bs[out].lsb(), logic.getTerm_true());
    sstat status = mainSolver.insertFormula(last_bit, &msg);

    if (status == s_True)
        return l_True;
    else if (status == s_False)
        return l_False;
    else return l_Undef;
}

lbool
BitBlaster::insertEq(PTRef tr, BVRef& out)
{
    assert(logic.isBVEq(tr) || logic.isBVOne(tr) || logic.isBVZero(tr));
    return insert(tr, out);
}

lbool
BitBlaster::insertOr(PTRef tr, BVRef& out)
{
    assert(logic.isBVLor(tr) || logic.isBVOne(tr) || logic.isBVZero(tr));
    return insert(tr, out);
}

bool
BitBlaster::assertLit (PtAsgn pta)
{
    // This needs to be re-thought.  I'd like to have this activation
    // logic in MainSolver somehow and use the incremental interface.
    assert( pta.tr != PTRef_Undef );
    Pterm& p = logic.getPterm(pta.tr);
    Var act_var = p.getVar();

    if ( ((pta.sgn == l_False) && (thandler.varToTerm(act_var) == logic.getTerm_true() ))
      || thandler.varToTerm(act_var) == logic.getTerm_false())
        return false;
    //
    // Activate clause for e
    //
    vec< Lit > clause;
    clause.push( mkLit( act_var, (pta.sgn == l_True ? false : true) ) );
    bool res = addClause( clause, pta.tr );

    return res;
}

lbool
BitBlaster::check( )
{
    const lbool res = solverP.solve( );
//    assert( res || (explanation.size() != 0) );
    return res;
}

void
BitBlaster::pushBacktrackPoint ( )
{
    solverP.pushBacktrackPoint( );
}

void 
BitBlaster::popBacktrackPoint ( )
{
    // Pop solver
    solverP.popBacktrackPoint( );
    solverP.restoreOK( );
    has_model = false;
}

char*
BitBlaster::getName(const char* base) const
{
    char* out;
    asprintf(&out, "%s%d", base, bs.size());
    return out;
}

void
BitBlaster::getBVVars(const char* base, vec<PTRef>& vars, int width)
{
    vars.growTo(width);
    for (int i = 0; i < width; i++) {
        char* bit_name;
        asprintf(&bit_name, ".%s%02d_", base, i);
        vars[i] = logic.mkBoolVar(getName(bit_name));
        free(bit_name);
    }
}

PTRef
BitBlaster::mkActVar(const char* base)
{
    char* name = getName(base);
    PTRef v = logic.mkBoolVar(name);
    free(name);
    return v;
}

//=============================================================================
// BitBlasting Routines

BVRef
BitBlaster::bbTerm(PTRef tr)
{
    //
    // BitBlasts predicates
    //
    if (logic.isBVEq(tr)) return bbEq           ( tr );
    if (logic.isBVSleq(tr)) return bbBvsle      ( tr );
    if (logic.isBVUleq(tr)) return bbBvule      ( tr );
    if (logic.isDistinct(tr)) return bbDistinct ( tr );
    // if ( e->isUp         ( ) ) return bbUp   ( e );
    //
    // BitBlasts terms
    //

//    if ( e->isConcat     ( ) ) return bbConcat     ( e );
//    if ( e->isExtract    ( ) ) return bbExtract    ( e );

    if (logic.isBVBwAnd(tr)) return bbBvand      (tr);
    if (logic.isBVBwOr(tr))  return bbBvor       (tr);
    if (logic.isBVBwXor(tr)) return bbBvxor      (tr);
    if (logic.isBVCompl(tr)) return bbBvcompl    (tr);
    if (logic.isBVNot(tr))   return bbBvlnot     (tr);
    if (logic.isBVLand(tr))  return bbBvland     (tr);
    if (logic.isBVLor(tr))   return bbBvlor      (tr);
    if (logic.isBVPlus(tr))  return bbBvadd      (tr);
    if (logic.isBVTimes(tr)) return bbBvmul      (tr);
    if (logic.isBVDiv(tr))   return bbBvudiv     (tr);
    if (logic.isBVMod(tr))   return bbBvurem     (tr);
//    if ( e->isSignExtend ( ) ) return bbSignExtend ( e );

    if ( logic.isVar(tr) )      return bbVar        ( tr );
    if ( logic.isConstant(tr) ) return bbConstant   ( tr );
    // if ( e->isUf         ( ) ) return bbUf         ( e );
    //
    // Exit if term is not handled
    //
    cerr << "term not handled (yet ?): " << logic.printTerm(tr) << "\n";
    return BVRef_Undef;
}

//
// Equality
//
BVRef
BitBlaster::bbEq(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.isEquality(tr));


    // Return previous result if computed
    if (bs.has(tr))
        return bs.getFromPTRef(tr);

    vec<PTRef> names;
    getBVVars("eq", names, bitwidth);

    Pterm& t = logic.getPterm(tr);
    assert( t.size() == 2 );
    PTRef lhs = t[0];
    PTRef rhs = t[1];

    assert( !(logic.isConstant(lhs)) || !(logic.isConstant(rhs)) );

    // Retrieve arguments' encodings
    BVRef bb_lhs = bbTerm(lhs);
    BVRef bb_rhs = bbTerm(rhs);

    assert( bs[bb_lhs].size( ) == bs[bb_rhs].size( ) );

    // Produce the result
    vec<PTRef> result_args;
    for ( unsigned i = 0 ; i < bs[bb_lhs].size() ; i ++ )
    {
        result_args.push(logic.mkEq(bs[bb_lhs][i], bs[bb_rhs][i]));
    }
    PTRef res = simplify( logic.mkAnd( result_args ) );
    vec<PTRef> tmp;
    tmp.growTo(bitwidth, logic.getTerm_false());
    tmp[0] = res;
    return bs.newBvector(names, tmp, mkActVar(s_bbEq), tr);
}

//
// Signed less than equal
//
BVRef
BitBlaster::bbBvsle(PTRef tr)
{
    assert(tr != PTRef_Undef);
    // assert( logic.isBvsle(tr) );

    // Return previous result if computed
    Pterm& t = logic.getPterm(tr);
    if (bs.has(tr))
        return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("sle", names, bitwidth);

    assert( t.size() == 2 );
    PTRef lhs = t[0];
    PTRef rhs = t[1];

    // Retrieve arguments' encodings
    BVRef bb_lhs = bbTerm( lhs );
    BVRef bb_rhs = bbTerm( rhs );
    assert( bs[bb_lhs].size( ) == bs[bb_rhs].size( ) );
    //
    // Produce lhs < rhs
    //
    PTRef lt_prev = PTRef_Undef;
    for ( unsigned i = 0 ; i < bs[bb_lhs].size() - 1 ; i ++ )
    {
        // Produce ~l[i] & r[i]
        PTRef not_l   = logic.mkNot( bs[bb_lhs][i] );
        PTRef lt_this = logic.mkAnd( not_l, bs[bb_rhs][i] );
        // Produce l[i] <-> r[i]
        PTRef eq_this = logic.mkEq( bs[bb_lhs][i], bs[bb_rhs][i]);
        if ( lt_prev != PTRef_Undef )
            lt_prev = logic.mkOr( lt_this, logic.mkAnd(eq_this, lt_prev) );
        else
            lt_prev = lt_this;
    }

    assert( lt_prev != PTRef_Undef );
    PTRef not_r   = logic.mkNot(bs[bb_rhs].lsb());
    PTRef neg_pos = logic.mkAnd(bs[bb_lhs].lsb(), not_r);
    PTRef eq_this = logic.mkEq(bs[bb_lhs].lsb(), bs[bb_rhs].lsb());
    PTRef lt_part = logic.mkOr(logic.mkAnd(eq_this, lt_prev), neg_pos) ;

    BVRef eq_part = bbTerm(logic.mkEq(lhs, rhs));
    //
    // Produce (lhs=rhs | lhs<rhs)
    //
    PTRef tr_out = simplify(logic.mkOr(bs[eq_part].lsb(), lt_part));

    // Save result and return
    vec<PTRef> asgns;
    asgns.growTo(bitwidth, logic.getTerm_false());
    asgns[0] = tr_out;
    return bs.newBvector(names, asgns, mkActVar(s_bbBvsle), tr);
}

//
// Unsigned less than equal
//
BVRef
BitBlaster::bbBvule(PTRef tr)
{
    assert(tr != PTRef_Undef);
    //
    // What ? Isn't it an eq ? Well lt are translated into le
    // in creation, still we want to encode le as if it was
    // an eq, as le = lt or eq
    //
    // Later comment: What did I mean ?? :-)
    //
    // assert( e->isBvule( ) );

    // Return previous result if computed
    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("ule", names, bitwidth);

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
    for (unsigned i = 0 ; i < bs[bb_lhs].size() ; i ++)
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

    PTRef lt_part = lt_prev;
    BVRef eq_part = bbTerm(logic.mkEq(lhs, rhs));
    //
    // Produce (lhs=rhs | lhs<rhs)
    //
    PTRef res = simplify(logic.mkOr(bs[eq_part].lsb(), lt_part));

    vec<PTRef> asgns;
    asgns.growTo(bitwidth, logic.getTerm_false());
    asgns[0] = res;

    // Save result and return
    return bs.newBvector(names, asgns, mkActVar(s_bbBvule), tr);
}

//
// Concatenation
//
BVRef
BitBlaster::bbConcat(PTRef tr)
{
    assert( tr != PTRef_Undef );

    if (bs.has(tr))
        return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("con", names, bitwidth);

    vec<PTRef> result;
    // Retrieve arguments and put on the stack
    for (int i = logic.getPterm(tr).size()-1; i >= 0; i--) {
        PTRef arg = logic.getPterm(tr)[i];
        BVRef bb_arg = bbTerm(arg);
        for (int j = 0; j < bs[bb_arg].size(); j++)
            result.push(bs[bb_arg][j]);
    }

    // Save result and return
    return bs.newBvector(names, result, mkActVar(s_bbConcat), tr);
}

//
// Extraction
//
BVRef
BitBlaster::bbExtract(PTRef tr)
{
    // Have a look at this, it probably shouldn't return 32 bits
    assert(tr != PTRef_Undef);

    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("ex", names, bitwidth);

    int lsb = 0, msb = 0;

    assert(logic.getPterm(tr).size() == 1 );
    PTRef arg = logic.getPterm(tr)[0];
    // Retrieve arguments' encodings
    BVRef bb_arg = bbTerm(arg);
    // Produce the result
    vec<PTRef> result;
    result.growTo(bitwidth, logic.getTerm_false());
    for ( int i = lsb, j = 0; i <= msb ; i ++ )
        result[j++] = bs[bb_arg][i];

    // Save result and return
    return bs.newBvector(names, result, mkActVar(s_bbExtract), tr);
}

//
// Bitwise AND
//
BVRef
BitBlaster::bbBvand(PTRef tr)
{
    assert(tr != PTRef_Undef);

    assert(logic.getPterm(logic.getPterm(tr)[0]).size() == logic.getPterm(logic.getPterm(tr)[1]).size()); // Should be e->get2nd( )->getWidth( )


    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("and", names, bitwidth);

    vec<BVRef> bb_args;

    // Bit-blast the arguments, and put the corresponding vectors
    // into bb_args.
    for (int i = 0; i < logic.getPterm(tr).size(); i++)
        bb_args.push(bbTerm(logic.getPterm(tr)[i]));

    int n_bits = bs[bb_args[0]].size(); // the number of bits in each argument
    int n_args = bb_args.size(); // the number of arguments
    // Iterate over all bits
    vec<PTRef> result;
    for (int i = 0; i < n_bits; i++) {
        vec<PTRef> and_args;
        // Iterate over all arguments
        for (int j = 0 ; j < bb_args.size(); j++) {
            assert(bs[bb_args[j]].size() == n_bits);
            and_args.push((bs[bb_args[j]])[i]);
        }
        result.push(logic.mkAnd(and_args));
    }

    return bs.newBvector(names, result, mkActVar(s_bbBvand), tr);
}

//
// Logical AND
//
BVRef
BitBlaster::bbBvland(PTRef tr)
{
    assert(tr != PTRef_Undef);



    if (bs.has(tr)) return bs[tr];

    assert(logic.getPterm(tr).size() == 2);

    // Allocate new result
    vec<PTRef> names;
    getBVVars("lan", names, bitwidth);

    vec<BVRef> bb_args;

    // Bit-blast the arguments, and put the corresponding vectors
    // into bb_args.
    PTRef arg1 = logic.getPterm(tr)[0];
    PTRef arg2 = logic.getPterm(tr)[1];

    BVRef bv1 = bbTerm(arg1);
    BVRef bv2 = bbTerm(arg2);

    assert(bs[bv1].size() == bs[bv2].size());
    vec<PTRef> result;
    //result.growTo(bitwidth, logic.getTerm_false());
    result.growTo(bs[bv1].size(), logic.getTerm_false());

    vec<PTRef> bv1_bits;
    vec<PTRef> bv2_bits;

    bs.copyAsgnTo(bv1, bv1_bits);
    bs.copyAsgnTo(bv2, bv2_bits);

    result[0] = logic.mkAnd(logic.mkOr(bv1_bits), logic.mkOr(bv2_bits));
//    for (int i = 1; i < result.size(); i++)
//        result[i] = logic.getTerm_false();

    return bs.newBvector(names, result, mkActVar(s_bbBvland), tr);
}


//
// Bitwise OR
//
BVRef
BitBlaster::bbBvor(PTRef tr)
{
    assert(tr != PTRef_Undef);

    if (bs.has(tr)) return bs[tr];


    // Allocate new result
    vec<PTRef> names;
    getBVVars("or", names, bitwidth);


    vec<PTRef> result;

    vec<BVRef> bb_args;

    // Bit-blast the arguments, and put the corresponding vectors
    // into bb_args.
    for (int i = 0; i < logic.getPterm(tr).size(); i++)
        bb_args.push(bbTerm(logic.getPterm(tr)[i]));

    int n_bits = bs[bb_args[0]].size(); // the number of bits in each argument
    int n_args = bb_args.size(); // the number of arguments
    // Iterate over all bits
    for (int i = 0; i < n_bits; i++) {
        vec<PTRef> and_args;
        // Iterate over all arguments
        for (int j = 0 ; j < bb_args.size(); j++) {
            assert(bs[bb_args[j]].size() == n_bits);
            and_args.push((bs[bb_args[j]])[i]);
        }
        result.push(logic.mkOr(and_args));
    }

    // Save result and return
    return bs.newBvector(names, result, mkActVar(s_bbBvor), tr);
}

//
// Logical OR
//
BVRef
BitBlaster::bbBvlor(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.getPterm(tr).size() == 2);

    if (bs.has(tr)) return bs[tr];


    // Allocate new result
    vec<PTRef> names;
    getBVVars("lor", names, bitwidth);

    vec<PTRef> result;
    result.growTo(bitwidth, logic.getTerm_false());

    PTRef arg1 = logic.getPterm(tr)[0];
    PTRef arg2 = logic.getPterm(tr)[1];

    BVRef bv1 = bbTerm(arg1);
    BVRef bv2 = bbTerm(arg2);

    vec<PTRef> bv1_bits;
    bs.copyAsgnTo(bv1, bv1_bits);
    vec<PTRef> bv2_bits;
    bs.copyAsgnTo(bv2, bv2_bits);

    result[0] = logic.mkOr(logic.mkOr(bv1_bits), logic.mkOr(bv2_bits));
//    for (int i = 1; i < result.size(); i++)
//        result[i] = logic.getTerm_false();

    // Save result and return
    return bs.newBvector(names, result, mkActVar(s_bbBvlor), tr);
}


//
// Bitwise XOR
//
BVRef
BitBlaster::bbBvxor(PTRef tr)
{
    assert(tr != PTRef_Undef);

    if (bs.has(tr)) return bs[tr];

    assert( logic.getPterm(tr).size() == 2 );

    // Allocate new result
    vec<PTRef> names;
    getBVVars("xor", names, bitwidth);

    // Allocate new result
    vec<PTRef> result;

    PTRef lhs = logic.getPterm(tr)[0];
    PTRef rhs = logic.getPterm(tr)[1];
    BVRef bb_lhs = bbTerm( lhs );
    BVRef bb_rhs = bbTerm( rhs );

    assert(bs[bb_lhs].size() == bs[bb_rhs].size());

    for ( int i = 0 ; i < bs[bb_lhs].size() ; i ++ )
        result.push( logic.mkXor(bs[bb_lhs][i], bs[bb_rhs][i]));

    return bs.newBvector(names, result, mkActVar(s_bbBvxor), tr);
}

//
// Bitwise complement
//
BVRef
BitBlaster::bbBvcompl(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.getPterm(tr).size() == 1);

    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("not", names, bitwidth);


    // Allocate new result
    vec<PTRef> result;

    PTRef arg = logic.getPterm(tr)[0];
    BVRef bb_arg = bbTerm(arg);

    for ( int i = 0 ; i < bs[bb_arg].size( ) ; i ++ )
        result.push(logic.mkNot(bs[bb_arg][i]));

    // Save result and return
    return bs.newBvector(names, result, mkActVar(s_bbBvcompl), tr);
}

//
// Logical NOT
//

BVRef
BitBlaster::bbBvlnot(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.getPterm(tr).size() == 1);

    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("lnot", names, bitwidth);


    // Allocate new result
    vec<PTRef> result;
    result.growTo(bitwidth, logic.getTerm_false());

    PTRef arg = logic.getPterm(tr)[0];
    BVRef bb_arg = bbTerm(arg);

    vec<PTRef> asgn;
    bs.copyAsgnTo(bb_arg, asgn);
    result[0] = logic.mkNot(logic.mkOr(asgn));
//    for ( int i = 1 ; i < bitwidth; i ++ )
//        result[i] = logic.getTerm_false();

    // Save result and return
    return bs.newBvector(names, result, mkActVar(s_bbBvlnot), tr);
}

BVRef
BitBlaster::bbBvadd(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert( logic.getPterm(tr).size() == 2 );

    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("add", names, bitwidth);

    // Allocate new result
    vec<PTRef> result;

    PTRef arg1 = logic.getPterm(tr)[0];
    PTRef arg2 = logic.getPterm(tr)[1];
    BVRef bb_arg1 = bbTerm(arg1);
    BVRef bb_arg2 = bbTerm(arg2);
    assert( bs[bb_arg1].size() == bs[bb_arg2].size() );

    PTRef carry = PTRef_Undef;

    int bw = bs[bb_arg1].size(); // the bit width
    for (int i = 0 ; i < bw; i++)
    {
        PTRef bit_1 = bs[bb_arg1][i];
        PTRef bit_2 = bs[bb_arg2][i];
        assert(bit_1 != PTRef_Undef);
        assert(bit_2 != PTRef_Undef);

        PTRef xor_1 = logic.mkXor(bit_1, bit_2);
        PTRef and_1 = logic.mkAnd(bit_1, bit_2);

        if (carry != PTRef_Undef)
        {
            PTRef xor_2 = logic.mkXor(xor_1, carry);
            PTRef and_2 = logic.mkAnd(xor_1, carry);
            carry = logic.mkOr(and_1, and_2);
            result.push(xor_2);
        }
        else
        {
            carry = and_1;
            result.push(xor_1);
        }
    }

    // Save result and return
    return bs.newBvector(names, result, mkActVar(s_bbBvadd), tr);
}

BVRef
BitBlaster::bbBvudiv(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.getPterm(tr).size() == 2);

    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("udi", names, bitwidth);

    //
    // Allocate new result
    //
    vec<PTRef> result;
    //
    // Garbage collect
    //

    vec<PTRef> minuend;
    PTRef arg1 = logic.getPterm(tr)[0];
    PTRef arg2 = logic.getPterm(tr)[1];
    BVRef dividend = bbTerm(arg1);
    BVRef divisor = bbTerm(arg2);
    assert(bs[divisor].size() == bs[dividend].size());
    //
    // Generate condition divisor != 0
    //
    PTRef zero = logic.getTerm_BVZero();
    PTRef div_eq_zero = bs[bbTerm(logic.mkEq(arg2, zero))].lsb();

    const unsigned size = bs[divisor].size( );
    result.growTo(size);
    //
    // Initialize minuend as 0..0 q[n-1]
    //
    minuend.push(bs[dividend][size - 1]);
    for ( unsigned i = 1 ; i < size ; i ++ )
        minuend.push(logic.getTerm_false());
    //
    // Main loop
    //
    for ( int i = size - 1 ; i >= 0 ; i -- )
    {
        //
        // Compute result[ i ] = !(minuend < divisor);
        //
        PTRef lt_prev = PTRef_Undef;
        for ( unsigned j = 0 ; j < size ; j ++ )
        {
            // Produce ~l[j] & r[j]
            PTRef not_l = logic.mkNot(minuend[j]);
            PTRef lt_this = logic.mkAnd(not_l, bs[divisor][j]);
            // Produce l[j] <-> r[j]
            PTRef eq_this = logic.mkEq(minuend[j], bs[divisor][j]);
            if ( lt_prev != PTRef_Undef )
                lt_prev = logic.mkOr(lt_this, logic.mkAnd(eq_this, lt_prev));
            else
                lt_prev = lt_this;
        }

        assert( lt_prev != PTRef_Undef);

        result[i] = logic.mkOr(div_eq_zero, logic.mkNot(lt_prev));
        PTRef bit_i = result[i];
        //
        // Construct subtrahend
        //
        vec<PTRef> subtrahend;
        for ( unsigned j = 0 ; j < size ; j ++ )
            subtrahend.push(logic.mkAnd(bit_i, bs[divisor][j]));

        //
        // Subtract and store in minuend
        //
        PTRef carry = PTRef_Undef;
        for (int j = 0; j < minuend.size(); j++ )
        {
            PTRef bit_1 = minuend[j];
            PTRef bit_2 = subtrahend[j];
            assert(bit_1 != PTRef_Undef);
            assert(bit_2 != PTRef_Undef);

            PTRef bit_2_neg = logic.mkNot(bit_2);
            PTRef xor_1 = logic.mkXor(bit_1, bit_2_neg);
            PTRef and_1 = logic.mkAnd(bit_1, bit_2_neg);

            if (carry != PTRef_Undef)
            {
                PTRef xor_2 = logic.mkXor(xor_1, carry);
                PTRef and_2 = logic.mkAnd(xor_1, carry);
                carry = logic.mkOr(and_1, and_2);
                minuend[j] = xor_2;
            }
            else
            {
                carry = and_1;
                minuend[j] = xor_1;
            }
        }

        carry = PTRef_Undef;

        //
        // Adds one, if bit_i is one
        //
        for (int j = 0 ; j < minuend.size( ) ; j++)
        {
            PTRef bit_1 = minuend[j];
            PTRef bit_2 = j == 0 ? logic.getTerm_true() : logic.getTerm_false();
            assert(bit_1 != PTRef_Undef);

            PTRef xor_1 = logic.mkXor(bit_1, bit_2);
            PTRef and_1 = logic.mkAnd(bit_1, bit_2);

            if (carry != PTRef_Undef)
            {
                PTRef xor_2 = logic.mkXor(xor_1, carry);
                PTRef and_2 = logic.mkAnd(xor_1, carry);
                carry = logic.mkOr(and_1, and_2);
                minuend[j] = xor_2;
            }
            else
            {
                carry = and_1;
                minuend[j] = xor_1;
            }
        }

        if ( i > 0 )
        {
            //
            // Prepare new minuend
            //
            //                M[i-1]
            //
            // O[2] O[1] O[0]
            //      N[2] N[1] N[0]
            //
            for (int j = size - 1 ; j >= 1 ; j --)
                minuend[j] = minuend[j - 1];
                minuend[0] = bs[dividend][i - 1];
        }
    }
    //
    // Save result and return
    //
    return bs.newBvector(names, result, mkActVar(s_bbBvudiv), tr);
}

BVRef
BitBlaster::bbBvurem(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.getPterm(tr).size() == 2);

    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("ure", names, bitwidth);

    //
    // Allocate new result
    //
    vec<PTRef> result;

    vec<PTRef> minuend;
    PTRef arg1 = logic.getPterm(tr)[0];
    PTRef arg2 = logic.getPterm(tr)[1];
    BVRef dividend = bbTerm(arg1);
    BVRef divisor = bbTerm(arg2);
    assert(bs[divisor].size( ) == bs[dividend].size( ));
    //
    // Generate condition divisor != 0
    //
    PTRef zero = logic.getTerm_BVZero();
    PTRef div_eq_zero = bs[bbTerm(logic.mkEq(arg2, zero))].lsb();

    const unsigned size = bs[divisor].size();
    result.growTo(size);
    //
    // Initialize minuend as 0..0 q[n-1]
    //
    minuend.push(bs[dividend][ size - 1 ]);
    for ( unsigned i = 1 ; i < size ; i ++ )
        minuend.push(logic.getTerm_false());
    //
    // Main loop
    //
    for ( int i = size - 1 ; i >= 0 ; i -- )
    {
        //
        // Compute result[ i ] = !(minuend < divisor);
        //
        PTRef lt_prev = PTRef_Undef;
        for ( unsigned j = 0 ; j < size ; j ++ )
        {
            // Produce ~l[j] & r[j]
            PTRef not_l   = logic.mkNot(minuend[j]);
            PTRef lt_this = logic.mkAnd(not_l, bs[divisor][j]);
            // Produce l[j] <-> r[j]
            PTRef eq_this = logic.mkEq(minuend[j], bs[divisor][j]);
            if (lt_prev != PTRef_Undef)
                lt_prev = logic.mkOr(lt_this, logic.mkAnd(eq_this, lt_prev));
            else
                lt_prev = lt_this;
        }

        assert(lt_prev != PTRef_Undef);
        PTRef bit_i = logic.mkNot(lt_prev);

        //
        // Construct subtrahend
        //
        vec<PTRef> subtrahend;
        for ( unsigned j = 0 ; j < size ; j ++ )
            subtrahend.push(logic.mkAnd(bit_i, bs[divisor][j]));
        //
        // Subtract and store in minuend
        //
        PTRef carry = PTRef_Undef;

        for( unsigned j = 0 ; j < minuend.size( ) ; j++ )
        {
            PTRef bit_1 = minuend[ j ];
            PTRef bit_2 = subtrahend[ j ];
            assert(bit_1 != PTRef_Undef);
            assert(bit_2 != PTRef_Undef);

            PTRef bit_2_neg = logic.mkNot(bit_2);
            PTRef xor_1 = logic.mkXor(bit_1, bit_2_neg);
            PTRef and_1 = logic.mkAnd(bit_1, bit_2_neg);

            if (carry != PTRef_Undef)
            {
                PTRef xor_2 = logic.mkXor(xor_1, carry);
                PTRef and_2 = logic.mkAnd(xor_1, carry);
                carry = logic.mkOr(and_1, and_2);
                minuend[j] = xor_2;
            }
            else
            {
                carry = and_1;
                minuend[j] = xor_1;
            }
        }

        carry = PTRef_Undef;

        //
        // Adds one, if bit_i is one
        //
        for (unsigned j = 0 ; j < minuend.size( ) ; j++)
        {
            PTRef bit_1 = minuend[ j ];
            PTRef bit_2 = j == 0 ? logic.getTerm_true() : logic.getTerm_false();
            assert(bit_1 != PTRef_Undef);

            PTRef xor_1 = logic.mkXor(bit_1, bit_2);
            PTRef and_1 = logic.mkAnd(bit_1, bit_2);

            if (carry != PTRef_Undef)
            {
                PTRef xor_2 = logic.mkXor(xor_1, carry);
                PTRef and_2 = logic.mkAnd(xor_1, carry);
                carry = logic.mkOr(and_1, and_2);
                minuend[j] = xor_2;
            }
            else
            {
                carry = and_1;
                minuend[ j ] = xor_1;
            }
        }

        if (i > 0)
        {
            //
            // Prepare new minuend
            //
            //                M[i-1]
            //
            // O[2] O[1] O[0]
            //      N[2] N[1] N[0]
            //
            for ( int j = size - 1 ; j >= 1 ; j -- )
                minuend[j] = minuend[j - 1];
            minuend[0] = bs[dividend][i - 1];
        }
        else
        {
            for ( unsigned j = 0 ; j < size ; j ++ )
            {
                result[j] = logic.mkOr(div_eq_zero, minuend[j]);
            }
        }
    }

    //
    // Save result and return
    //
    return bs.newBvector(names, result, mkActVar(s_bbBvurem), tr);
}

BVRef
BitBlaster::bbBvmul(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.getPterm(tr).size() == 2 );

    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("mul", names, bitwidth);

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

        assert( addend.size( ) == size );
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

    return bs.newBvector(names, result, mkActVar(s_bbBvmul), tr);
}

BVRef
BitBlaster::bbSignExtend(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.getPterm(tr).size() == 1 );

    // Return previous result if computed
    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("se", names, bitwidth);

    vec<PTRef> result;

    PTRef x = logic.getPterm(tr)[0];
    BVRef bb_x = bbTerm(x);
    // Copy x
    unsigned i;
    for ( i = 0 ; i < bs[bb_x].size( ) ; i ++ )
        result.push(bs[bb_x][i]);
    // Sign extend
    for ( ; (int)i < bitwidth; i ++ ) // Should be bit width of what?
        result.push(bs[bb_x].lsb());

    return bs.newBvector(names, result, mkActVar(s_bbSignExtend), tr);
}

BVRef
BitBlaster::bbVar(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.isVar(tr));

    if (bs.has(tr)) return bs[tr];

    // Allocate new result
    vec<PTRef> names;
    getBVVars("bv", names, bitwidth);

    vec<PTRef> result;
    names.copyTo(result);

    // Save variable
    variables.push(tr);


    BVRef rval = bs.newBvector(names, result, mkActVar(s_bbVar), tr);

    return rval;
}

BVRef
BitBlaster::bbConstant(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.isConstant(tr));

    if (bs.has(tr)) return bs[tr];
    // Allocate new result
    vec<PTRef> names;
    getBVVars("c", names, bitwidth);

    vec<PTRef> asgns;
    asgns.growTo(bitwidth,  logic.getTerm_false());
//    for (int i = 0; i < bitwidth; i++) {
//        asgns[i]  = logic.getTerm_false();
//    }

    if (logic.isTrue(tr))
        asgns[0] = logic.getTerm_true();
    else if (logic.isFalse(tr))
        ; // already ok
    else
    {
        const std::string value = logic.getSymName(tr);

        assert(value.length() == bitwidth);
        for (unsigned i = 0 ; i < bitwidth; i ++)
        {
            asgns[i] = value[bitwidth-i-1] == '1' ? logic.getTerm_true() : logic.getTerm_false();
        }
    }
    // Save result and return
    return bs.newBvector(names, asgns, mkActVar(s_bbConstant), tr);
}

/*
vector< Enode * > &
BitBlaster::bbUf( Enode * )
{
  assert( false );
}

vector< Enode * > &
BitBlaster::bbUp( Enode * )
{
  assert( false );
}
*/

BVRef
BitBlaster::bbDistinct(PTRef tr)
{
    assert(tr != PTRef_Undef);
    assert(logic.isDistinct(tr));

    if (bs.has(tr)) return bs[tr];

    vec<PTRef> vars;
    getBVVars("d", vars, bitwidth);

    vec<PTRef> result;
    result.growTo(bitwidth, logic.getTerm_false());
    vec<PTRef> args;

    for (int i = 0; i < logic.getPterm(tr).size(); i++)
        args.push(logic.getPterm(tr)[i]);
    //
    // Quadratic encoding
    //

    vec<PTRef> res_args;
    for (int i = 0; i < logic.getPterm(tr).size()-1; i++)
    {
        for (int j = i+1; j < logic.getPterm(tr).size(); j++)
        {
            BVRef bb_pair = bbTerm(logic.mkEq(args[i], args[j]));
            assert(bs[bb_pair].size() == 1);
            res_args.push(logic.mkNot(bs[bb_pair].lsb()));
        }
    }

    result[0] = logic.mkAnd(res_args);

    return bs.newBvector(vars, result, mkActVar(s_bbDistinct), tr);
}

bool
BitBlaster::addClause(vec< Lit > & c, PTRef tr)
{
    return solverP.addClause(c);
}

//=============================================================================
// CNFization Routines
//
//Var
//BitBlaster::cnfizeAndGiveToSolver( Enode * bb, Enode * atom )
//{
//  // Stack for unprocessed enodes
//  vector< Enode * > unprocessed_enodes;
//  // Cnfize and give to solver
//  unprocessed_enodes.push_back( bb );
//
//  while( !unprocessed_enodes.empty( ) )
//  {
//    Enode * enode = unprocessed_enodes.back( );
//    assert( enode->hasSortBool( ) );
//    //
//    // Skip if the node has already been processed before
//    //
//    if ( (int)cnf_cache.size( ) <= enode->getId( ) )
//      cnf_cache.resize( enode->getId( ) + 1, lit_Undef );
//    if ( cnf_cache[ enode->getId( ) ] != lit_Undef )
//    {
//      unprocessed_enodes.pop_back( );
//      continue;
//    }
//
//    bool unprocessed_children = false;
//    Enode * arg_list;
//    for ( arg_list = enode->getCdr( ) ;
//          arg_list != E.enil ;
//          arg_list = arg_list->getCdr( ) )
//    {
//      Enode * arg = arg_list->getCar( );
//      assert( arg->isTerm( ) );
//      //
//      // Push children if not processed already
//      //
//      if ( (int)cnf_cache.size( ) <= arg->getId( ) )
//        cnf_cache.resize( arg->getId( ) + 1, lit_Undef );
//      if ( cnf_cache[ arg->getId( ) ] == lit_Undef )
//      {
//        unprocessed_enodes.push_back( arg );
//        unprocessed_children = true;
//      }
//    }
//    //
//    // SKip if unprocessed children
//    //
//    if ( unprocessed_children )
//      continue;
//
//    unprocessed_enodes.pop_back( );
//    Lit result = lit_Undef;
//    //
//    // At this point, every child has been processed
//    //
//    //
//    // Do the actual cnfization, according to the node type
//    //
//    if ( enode->isTrue( ) )
//      result = constTrue;
//    else if ( enode->isFalse( ) )
//      result = constFalse;
//    else if ( enode->isAtom( ) )
//    {
//      // Allocate a new boolean variable for this atom
//      Var var = solverP.newVar( );
//      // Keep track to retrieve model
//      assert( cnf_var.find( enode->getId( ) ) == cnf_var.end( ) );
//      cnf_var[ enode->getId( ) ] = var;
//      result = Lit( var );
//    }
//    else if ( enode->isNot( ) )
//    {
//      assert( (int)cnf_cache.size( ) > enode->getId( ) );
//
//      Lit arg_def = cnf_cache[ enode->get1st( )->getId( ) ];
//      assert( arg_def != lit_Undef );
//      // Toggle variable
//      result = ~arg_def;
//    }
//    else
//    {
//      //
//      // Allocates a new variable for definition
//      //
//      Var var = solverP.newVar( );
//      //
//      // Store correspondence
//      //
//      result = Lit( var );
//      //
//      // Handle remaining cases
//      //
//
//      Enode * atom_ = ( enode == bb ? atom : NULL );
//
//      if ( enode->isAnd( ) )
//        cnfizeAnd( enode, result, atom_ );
//      else if ( enode->isOr( ) )
//        cnfizeOr ( enode, result, atom_ );
//      /*
//      else if ( enode->isIff( ) )
//        cnfizeIff( enode, result, atom_ );
//      */
//      else if ( enode->isXor( ) )
//        cnfizeXor( enode, result, atom_ );
//      else
//        opensmt_error2( "operator not handled ", enode->getCar( ) );
//    }
//
//    assert( result != lit_Undef );
//    assert( cnf_cache[ enode->getId( ) ] == lit_Undef );
//    // Store result
//    cnf_cache[ enode->getId( ) ] = result;
//  }
//
//  //
//  // Add an activation variable
//  //
//  assert( cnf_cache[ bb->getId( ) ] != lit_Undef );
//
//  Lit l = cnf_cache[ bb->getId( ) ];
//
//  Var  act = solverP.newVar( );
//  Lit lact = Lit( act );
//  vec< Lit > clause;
//  //
//  // Adds ~act | l
//  //
//  clause.push( ~lact );
//  clause.push( l );
//  addClause( clause, atom );
//  //
//  // Adds act | ~l
//  //
//  clause.pop( );
//  clause.pop( );
//  clause.push( lact );
//  clause.push( ~l );
//  addClause( clause, atom );
//
//  return act;
//}

//void
//BitBlaster::cnfizeAnd( Enode * enode, Lit def, Enode * atom )
//{
//  assert( enode );
//  Enode * list = NULL;
//  //
//  // ( a_0 & ... & a_{n-1} )
//  //
//  // <=>
//  //
//  // aux = ( -aux | a_0 ) & ... & ( -aux | a_{n-1} ) & ( aux & -a_0 & ... & -a_{n-1} )
//  //
//  vec< Lit > little_clause;
//  vec< Lit > big_clause;
//  little_clause.push( ~def );
//  big_clause   .push(  def );
//  for ( list = enode->getCdr( )
//      ; list != E.enil
//      ; list = list->getCdr( ) )
//  {
//    Lit arg = cnf_cache[ list->getCar( )->getId( ) ];
//    assert( arg != lit_Undef );
//    little_clause.push(  arg );
//    big_clause   .push( ~arg );
//    addClause( little_clause, atom );
//    little_clause.pop( );
//  }
//  addClause( big_clause, atom );
//}

//void
//BitBlaster::cnfizeOr( Enode * enode, Lit def, Enode * atom )
//{
//  assert( enode );
//  Enode * list = NULL;
//  //
//  // ( a_0 | ... | a_{n-1} )
//  //
//  // <=>
//  //
//  // aux = ( aux | -a_0 ) & ... & ( aux | -a_{n-1} ) & ( -aux | a_0 | ... | a_{n-1} )
//  //
//  vec< Lit > little_clause;
//  vec< Lit > big_clause;
//  little_clause.push(  def );
//  big_clause   .push( ~def );
//  for ( list = enode->getCdr( )
//      ; list != E.enil
//      ; list = list->getCdr( ) )
//  {
//    Lit arg = cnf_cache[ list->getCar( )->getId( ) ];
//    little_clause.push( ~arg );
//    big_clause   .push(  arg );
//    addClause( little_clause, atom );
//    little_clause.pop( );
//  }
//  addClause( big_clause, atom );
//}

//void
//BitBlaster::cnfizeXor( Enode * enode, Lit def, Enode * atom )
//{
//  assert( enode );
//  Enode * list = enode->getCdr( );
//  //
//  // ( a_0 xor a_1 )
//  //
//  // <=>
//  //
//  // aux = ( -aux |  a_0 | a_1 ) & ( -aux | -a_0 | -a_1 ) &
//  //       (  aux | -a_0 | a_1 ) & (  aux |  a_0 |  a_1 ) 
//  //
//  assert( list->getArity( ) == 2 );
//  Lit arg0 = cnf_cache[ list->getCar( )->getId( ) ];
//  Lit arg1 = cnf_cache[ list->getCdr( )->getCar( )->getId( ) ];
//  vec< Lit > clause;
//
//  clause.push( ~def );
//
//  // First clause
//  clause  .push( ~arg0 );
//  clause  .push( ~arg1 );
//  addClause( clause, atom );
//  clause  .pop( );
//  clause  .pop( );
//
//  // Second clause
//  clause  .push(  arg0 );
//  clause  .push(  arg1 );
//  addClause( clause, atom );
//  clause  .pop( );
//  clause  .pop( );
//
//  clause.pop( );
//  clause.push( def );
//
//  // Third clause
//  clause  .push( ~arg0 );
//  clause  .push(  arg1 );
//  addClause( clause, atom );
//  clause  .pop( );
//  clause  .pop( );
//
//  // Fourth clause
//  clause  .push(  arg0 );
//  clause  .push( ~arg1 );
//  addClause( clause, atom );
//}

//void
//BitBlaster::cnfizeIff( Enode * enode, Lit def, Enode * atom )
//{
//  assert( enode );
//  Enode * list = enode->getCdr( );
//  //
//  // ( a_0 <-> a_1 )
//  //
//  // <=>
//  //
//  // aux = ( -aux |  a_0 | -a_1 ) & ( -aux | -a_0 |  a_1 ) &
//  //       (  aux |  a_0 |  a_1 ) & (  aux | -a_0 | -a_1 )
//  //
//  assert( list->getArity( ) == 2 );
//  Lit arg0 = cnf_cache[ list->getCar( )->getId( ) ];
//  Lit arg1 = cnf_cache[ list->getCdr( )->getCar( )->getId( ) ];
//  vec< Lit > clause;
//
//  clause.push( ~def );
//
//  // First clause
//  clause  .push(  arg0 );
//  clause  .push( ~arg1 );
//  addClause( clause, atom );
//  clause  .pop( );
//  clause  .pop( );
//
//  // Second clause
//  clause  .push( ~arg0 );
//  clause  .push(  arg1 );
//  addClause( clause, atom );
//  clause  .pop( );
//  clause  .pop( );
//
//  clause.pop( );
//  clause.push( def );
//
//  // Third clause
//  clause  .push( ~arg0 );
//  clause  .push( ~arg1 );
//  addClause( clause, atom );
//  clause  .pop( );
//  clause  .pop( );
//
//  // Fourth clause
//  clause  .push(  arg0 );
//  clause  .push(  arg1 );
//  addClause( clause, atom );
//}

//void 
//BitBlaster::cnfizeIfthenelse( Enode * enode, Lit def, Enode * atom )
//{
//  assert( enode );
//  Enode * list = enode->getCdr( );
//  //
//  // ( if a_0 then a_1 else a_2 )
//  //
//  // <=>
//  //
//  // aux = ( -aux | -a_0 |  a_1 ) &
//  //       ( -aux |  a_0 |  a_2 ) &
//  //       (  aux | -a_0 | -a_1 ) &
//  //       (  aux |  a_0 | -a_2 )
//  //
//  assert( list->getArity( ) == 2 );
//  Lit arg0 = cnf_cache[ list->getCar( )->getId( ) ];
//  Lit arg1 = cnf_cache[ list->getCdr( )->getCar( )->getId( ) ];
//  vec< Lit > clause;
//
//  clause.push( ~def );
//
//  // First clause
//  clause  .push( ~arg0 );
//  clause  .push(  arg1 );
//  addClause( clause, atom );
//  clause  .pop( );
//  clause  .pop( );
//
//  // Second clause
//  clause  .push(  arg0 );
//  clause  .push(  arg1 );
//  addClause( clause, atom );
//  clause  .pop( );
//  clause  .pop( );
//
//  clause.pop( );
//  clause.push( def );
//
//  // Third clause
//  clause  .push( ~arg0 );
//  clause  .push( ~arg1 );
//  addClause( clause, atom );
//  clause  .pop( );
//  clause  .pop( );
//
//  // Fourth clause
//  clause  .push(  arg0 );
//  clause  .push( ~arg1 );
//  addClause( clause, atom );
//}

void
BitBlaster::cleanGarbage( )
{
}

PTRef BitBlaster::simplify( PTRef formula )
{
    assert(formula != PTRef_Undef);

    Map<PTRef,PTRef,PTRefHash> seen;

    vec<PTRef> unprocessed_terms;
    unprocessed_terms.push(formula);
    //
    // Visit the DAG of the formula from the leaves to the root
    //
    while (unprocessed_terms.size() != 0)
    {
        PTRef tr = unprocessed_terms.last();
        //
        // Skip if the node has already been processed before
        //
        if (seen.has(tr))
        {
            unprocessed_terms.pop();
            continue;
        }

        bool unprocessed_children = false;
        Pterm& t = logic.getPterm(tr);
        for (int i = 0; i < t.size(); i++) {
            PTRef arg = t[i];
            if (!seen.has(arg)) {
                unprocessed_terms.push(arg);
                unprocessed_children = true;
            }
        }
        //
        // SKip if unprocessed_children
        //
        if ( unprocessed_children )
          continue;

        unprocessed_terms.pop();
        PTRef result = PTRef_Undef;

        if ( logic.isAnd(tr) && logic.getPterm(tr).size() == 2)
        {
            PTRef x = seen[logic.getPterm(tr)[0]];
            PTRef y = seen[logic.getPterm(tr)[1]];
            assert( x != PTRef_Undef );
            assert( y != PTRef_Undef );
            //
            // Rule 1
            //
            // (and x (not x)) --> false
            //
            if ( ( logic.isNot(x) && logic.getPterm(x)[0] == y )
              || ( logic.isNot(y) && logic.getPterm(y)[0] == x))
                result = logic.getTerm_false();
            //
            // Rule 2
            //
            // (and (not z) (not w)) --> (not (or z w))
            //
            else if (logic.isNot(x) && logic.isNot(y))
            {
                PTRef z = logic.getPterm(x)[0];
                PTRef w = logic.getPterm(y)[0];
                assert( z != PTRef_Undef );
                assert( w != PTRef_Undef );
                result = logic.mkNot(logic.mkOr(z, w));
            }
        }
        else if ( logic.isOr(tr) && logic.getPterm(tr).size() == 2 )
        {
            PTRef x = seen[logic.getPterm(tr)[0]];
            PTRef y = seen[logic.getPterm(tr)[1]];
            assert( x != PTRef_Undef );
            assert( y != PTRef_Undef );
            //
            // Rule 3
            //
            // (or x (and (not x) z)) --> (or x z))
            //
            if ( logic.isAnd(y)
              && (logic.getPterm(y).size() == 2)
              && logic.isNot(logic.getPterm(y)[0])
              && (logic.getPterm(logic.getPterm(y)[0])[0] == x) )
            {
                PTRef z = logic.getPterm(y)[1];
                result = logic.mkOr(x, z);
            }
            //
            // Rule 4
            //
            // (or (and (not y) z) y) --> (or z y))
            //
            if ( logic.isAnd(x)
              && logic.getPterm(x).size() == 2
              && logic.isNot(logic.getPterm(x)[0])
              && logic.getPterm(logic.getPterm(x)[0])[0] == y)
            {
                PTRef z = logic.getPterm(x)[1];
                result = logic.mkOr(y, z);
            }
        }

        if (result == PTRef_Undef)
        {
            result = tr;
            //result = E.copyEnodeEtypeTermWithCache( enode, true );
        }

        assert(result != PTRef_Undef);
        assert(!seen.has(tr));
        seen.insert(tr, result);
    }

    PTRef new_formula = seen[formula];
    assert(new_formula != PTRef_Undef);
    return new_formula;
}

//
// Compute the number of incoming edges for e and children
//
//void BitBlaster::computeIncomingEdges( Enode * e, map< int, int > & enodeid_to_incoming_edges )
//{
//  assert( e );
//
//  if ( !e->isBooleanOperator( ) )
//    return;
//
//  for ( Enode * list = e->getCdr( ) ;
//        !list->isEnil( ) ;
//        list = list->getCdr( ) )
//  {
//    Enode * arg = list->getCar( );
//    map< int, int >::iterator it = enodeid_to_incoming_edges.find( arg->getId( ) );
//    if ( it == enodeid_to_incoming_edges.end( ) )
//      enodeid_to_incoming_edges[ arg->getId( ) ] = 1;
//    else
//      it->second ++;
//    computeIncomingEdges( arg, enodeid_to_incoming_edges );
//  }
//}

//
// Rewrite formula with maximum arity for operators
//
//Enode * BitBlaster::rewriteMaxArity( Enode * formula, map< int, int > & enodeid_to_incoming_edges )
//{
//  assert( formula );
//
//  vector< Enode * > unprocessed_enodes;       // Stack for unprocessed enodes
//  unprocessed_enodes.push_back( formula );    // formula needs to be processed
//  map< int, Enode * > cache;                  // Cache of processed nodes
//  //
//  // Visit the DAG of the formula from the leaves to the root
//  //
//  while( !unprocessed_enodes.empty( ) )
//  {
//    Enode * enode = unprocessed_enodes.back( );
//    //
//    // Skip if the node has already been processed before
//    //
//    if ( cache.find( enode->getId( ) ) != cache.end( ) )
//    {
//      unprocessed_enodes.pop_back( );
//      continue;
//    }
//
//    bool unprocessed_children = false;
//    Enode * arg_list;
//    for ( arg_list = enode->getCdr( ) ;
//          arg_list != E.enil ;
//          arg_list = arg_list->getCdr( ) )
//    {
//      Enode * arg = arg_list->getCar( );
//
//      assert( arg->isTerm( ) );
//      //
//      // Push only if it is an unprocessed boolean operator
//      //
//      if ( arg->isBooleanOperator( )
//        && cache.find( arg->getId( ) ) == cache.end( ) )
//      {
//        unprocessed_enodes.push_back( arg );
//        unprocessed_children = true;
//      }
//      //
//      // If it is an atom (either boolean or theory) just
//      // store it in the cache
//      //
//      else if ( arg->isAtom( ) )
//      {
//        cache.insert( make_pair( arg->getId( ), arg ) );
//      }
//    }
//    //
//    // SKip if unprocessed_children
//    //
//    if ( unprocessed_children )
//      continue;
//
//    unprocessed_enodes.pop_back( );
//    Enode * result = NULL;
//    //
//    // At this point, every child has been processed
//    //
//    assert ( enode->isBooleanOperator( ) );
//
//    if ( enode->isAnd( ) 
//      || enode->isOr ( ) )
//    {
//      assert( enode->isAnd( ) || enode->isOr( ) );
//      //
//      // Construct the new lists for the operators
//      //
//      result = mergeEnodeArgs( enode, cache, enodeid_to_incoming_edges );
//    }
//    else
//    {
//      result = enode;
//    }
//
//    assert( result );
//    assert( cache.find( enode->getId( ) ) == cache.end( ) );
//    cache[ enode->getId( ) ] = result;
//  }
//
//  Enode * top_enode = cache[ formula->getId( ) ];
//  return top_enode;
//}

//
// Merge collected arguments for nodes
//
//Enode * BitBlaster::mergeEnodeArgs( Enode * e
//                                  , map< int, Enode * > & cache
//                                  , map< int, int > & enodeid_to_incoming_edges )
//{
//  assert( e->isAnd( ) || e->isOr( ) );
//
//  Enode * e_symb = e->getCar( );
//  vector< Enode * > new_args;
//
//  for ( Enode * list = e->getCdr( ) ;
//        !list->isEnil( ) ;
//        list = list->getCdr( ) )
//  {
//    Enode * arg = list->getCar( );
//    Enode * sub_arg = cache[ arg->getId( ) ];
//    Enode * sym = arg->getCar( );
//
//    if ( sym->getId( ) != e_symb->getId( ) )
//    {
//      new_args.push_back( sub_arg );
//      continue;
//    }
//
//    assert( enodeid_to_incoming_edges.find( arg->getId( ) ) != enodeid_to_incoming_edges.end( ) );
//    assert( enodeid_to_incoming_edges[ arg->getId( ) ] >= 1 );
//
//    if ( enodeid_to_incoming_edges[ arg->getId( ) ] > 1 )
//    {
//      new_args.push_back( sub_arg );
//      continue;
//    }
//
//    for ( Enode * sub_arg_list = sub_arg->getCdr( ) ;
//          !sub_arg_list->isEnil( ) ;
//          sub_arg_list = sub_arg_list->getCdr( ) )
//      new_args.push_back( sub_arg_list->getCar( ) );
//  }
//
//  Enode * new_list = const_cast< Enode * >(E.enil);
//
//  while ( !new_args.empty( ) )
//  {
//    new_list = E.cons( new_args.back( ), new_list );
//    new_args.pop_back( );
//  }
//
//  return E.cons( e_symb, new_list );
//}

void BitBlaster::computeModel( )
{
    model.clear();
    for ( unsigned i = 0 ; i < variables.size( ) ; i++ )
    {
        PTRef e = variables[ i ];
        Real value = 0;
        Real coeff = 1;
        // Retrieve bitblasted vector
        BVRef blast = bs[e];
        for (int j = 0; j < bs[blast].size(); j++)
        {
            PTRef b = bs[blast][j];
            Var var = logic.getPterm(b).getVar();
            Real bit = solverP.modelValue(mkLit(var)) == l_False ? 0 : 1;
            value = value + coeff * bit;
            coeff = Real( 2 ) * coeff;
        }
        ValPair v(e, value.get_str().c_str());

        model.insert(e, v);
    }
    has_model = true;
}

ValPair BitBlaster::getValue(PTRef tr)
{
    assert(has_model);
    return model[tr];
}

lbool
BitBlaster::notifyEquality(PTRef tr)
{
    assert(logic.isEquality(tr));
    Pterm &t =  logic.getPterm(tr);
    PTRef eq_arg0 = t[0];
    PTRef eq_arg1 = t[1];
    assert(bs.isBound(eq_arg0));
    assert(bs.isBound(eq_arg1));
    PTRef bv_tr0 = bs.getBoundPTRef(eq_arg0);
    PTRef bv_tr1 = bs.getBoundPTRef(eq_arg1);

    BVRef bv0_r = bs[bv_tr0];
    BVRef bv1_r = bs[bv_tr1];
    assert(bs[bv0_r].size() == bs[bv1_r].size());

    vec<PTRef> and_args;
    for (int i = 0; i < bs[bv0_r].size(); i++)
        and_args.push(logic.mkEq(bs[bv0_r][i], bs[bv1_r][i]));
    PTRef iff_tr = logic.mkEq(tr, logic.mkAnd(and_args));

    char* msg;
    sstat status = mainSolver.insertFormula(iff_tr, &msg);

    if (status == s_True)
        return l_True;
    else if (status == s_False)
        return l_False;
    else
        return l_Undef;
}

lbool
BitBlaster::glueBtoUF(BVRef br, PTRef tr)
{
    /*
    char* msg;

    vec<PTRef> bv;
    bs.copyTo(br, bv);
    PTRef eq_tr = logic.mkGlueBtoUF(bv, tr);
    sstat status = mainSolver.insertFormula(eq_tr, &msg);
    if (status == s_True)
        return l_True;
    else if (status == s_False)
        return l_False;
    else
        return l_Undef;
    */
    return l_Undef;
}

lbool
BitBlaster::glueUFtoB(PTRef tr, BVRef br)
{
    /*
    char* msg;
    vec<PTRef> bv;
    bs.copyTo(br, bv);
    PTRef and_tr = logic.mkGlueUFtoB(tr, bv);
    bs.bindPTRefToBVRef(tr,br);
    sstat status = mainSolver.insertFormula(and_tr, &msg);
    if (status == s_True)
        return l_True;
    else if (status == s_False)
        return l_False;
    else
        return l_Undef;
    */
    return l_Undef;
}

lbool
BitBlaster::glueUFtoUF(PTRef tr1, PTRef tr2)
{
    /*
    BVRef br1 = bs.getBoundBVRef(tr1);
    BVRef br2 = bs.getBoundBVRef(tr2);

    vec<PTRef> and_args;
    for (int i = 0; i < bs[br1].size(); i++)
        and_args.push(logic.mkEq(bs[br1][i], bs[br2][i]));
    PTRef iff_tr = logic.mkEq(logic.mkEq(tr1, tr2), logic.mkAnd(and_args));

    char* msg;
    sstat status = mainSolver.insertFormula(iff_tr, &msg);

    if (status == s_True)
        return l_True;
    else if (status == s_False)
        return l_False;
    else
        return l_Undef;
*/
    return l_Undef;
}
