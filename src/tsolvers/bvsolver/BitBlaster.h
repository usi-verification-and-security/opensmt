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

#ifndef BITBLASTER_H
#define BITBLASTER_H

#include "SimpSMTSolver.h"
#include "MainSolver.h"
#include "Otl.h"
#include "BVStore.h"
#include "BVLogic.h"

class BitBlaster
{
public:

    BitBlaster ( SolverId
               , SMTConfig &
               , MainSolver&
               , BVLogic&
               , vec<PtAsgn> &
               , vec<DedElem> &
               , vec<PTRef> & );
    ~BitBlaster ( );

    lbool inform             (PTRef); // For the interface for bitvector solver
    lbool check              ( );
    bool  assertLit          (PtAsgn);

    lbool insertEq           (PTRef tr, BVRef& out); // For the interface for theory refinement
    lbool insertOr           (PTRef tr, BVRef& out); // For the interface for theory refinement

    void pushBacktrackPoint  ( );
    void popBacktrackPoint   ( );

    void    computeModel     ( );
    ValPair getValue         (PTRef);

    void  bindCUFToBV        (PTRef tr_cuf, PTRef tr_bv) { bs.bindCUFToBV(tr_cuf, tr_bv); }
    lbool notifyEquality     (PTRef tr_eq);
    lbool glueBtoUF          (BVRef br, PTRef tr);  // (= tr (c br_1 ... br_32))
    lbool glueUFtoB          (PTRef tr, BVRef br);  // (= br_0 (e0 tr)) /\ ... /\ (= br_32 (e32 tr))
    lbool glueUFtoUF         (PTRef tr1, PTRef tr2); // (= uf1 uf2) <-> (and (= .b00_0 .b00_1) ... (= .b31_0 .b31_1))
    PTRef mkCollate32        (vec<PTRef>& bits);
    PTRef mkExtract          (PTRef tr, int i);
private:
    BVRef bbTerm             (PTRef);
    lbool insert             (PTRef tr, BVRef& out); // The unsafe interface for theory refinement
    BVRef          updateCache  (PTRef tr);
    SMTConfig &    config;                        // Configuration
    MainSolver&    mainSolver;
    BVLogic&       logic;                         // Egraph store
    THandler&      thandler;
    SimpSMTSolver& solverP;                       // Solver with proof logger

    bool addClause ( vec< Lit > &, PTRef );

    static const char* s_bbEq;
    static const char* s_bbAnd;
    static const char* s_bbBvsle;
    static const char* s_bbBvule;
    static const char* s_bbConcat;
    static const char* s_bbExtract;
    static const char* s_bbBvand;
    static const char* s_bbBvland;
    static const char* s_bbBvor;
    static const char* s_bbBvlor;
    static const char* s_bbBvxor;
    static const char* s_bbBvcompl;
    static const char* s_bbBvlnot;
    static const char* s_bbBvadd;
    static const char* s_bbBvmul;
    static const char* s_bbBvudiv;
    static const char* s_bbBvurem;
    static const char* s_bbSignExtend;
    static const char* s_bbVar;
    static const char* s_bbConstant;
    static const char* s_bbDistinct;
    char* getName(const char* base) const;
    void  getBVVars(const char* base, vec<PTRef>& vars, int width);
    PTRef mkActVar(const char* base);
    // Predicates
    BVRef bbEq         (PTRef);
    BVRef bbBvsle      (PTRef);
    BVRef bbBvule      (PTRef);
    // Terms
    BVRef bbConcat     (PTRef);
    BVRef bbExtract    (PTRef);
    BVRef bbBvand      (PTRef);
    BVRef bbBvland     (PTRef);
    BVRef bbBvor       (PTRef);
    BVRef bbBvlor      (PTRef);
    BVRef bbBvxor      (PTRef);
    BVRef bbBvcompl    (PTRef);
    BVRef bbBvlnot     (PTRef);
    BVRef bbBvadd      (PTRef);
    BVRef bbBvmul      (PTRef);
    BVRef bbBvudiv     (PTRef);
    BVRef bbBvurem     (PTRef);
    BVRef bbSignExtend (PTRef);
    BVRef bbVar        (PTRef);
    BVRef bbConstant   (PTRef);
    BVRef bbDistinct   (PTRef);

    PTRef bbBvadd_carryonly(PTRef sum, PTRef cin); // for signed comparison
  // Not yet considered
  // vector< Enode * > & bbUf         ( Enode * );
  // vector< Enode * > & bbUp         ( Enode * );
    void     cleanGarbage          ( );                            // Clean garbage on demand

    PTRef    simplify              ( PTRef );                    // Further simplifications
//    Enode *  rewriteMaxArity       ( Enode *
//                                   , map< int, int > & );
//    void     computeIncomingEdges  ( Enode *
//                                    , map< int, int > & );          // Computes the list of incoming edges for a node
//    Enode *  mergeEnodeArgs        ( Enode *
//                                    , map< int, Enode * > &
//                                    , map< int, int > & );          // Rewrite terms using maximum arity

    Lit                             constTrue;                     // Constant literal set to true
    Lit                             constFalse;                    // Constant literal set to false

    BVStore                         bs;

    vector< Lit >                   cnf_cache;                     // Global cache for cnfizer
    vector< Var >                   enode_id_to_var;               // Theory atom to Minisat Var correspondence
    vector< Enode * >               var_to_enode;                  // Minisat Var to Theory Atom correspondence


    vec<PtAsgn> &                   explanation;                   // Reference to explanation
    vec<DedElem> &                  deductions;                    // Reference to deductions
    vec<PTRef> &                    suggestions;                   // Reference to suggestions

    vec<PTRef>                      variables;                     // Variables
    map< int, Var >                 cnf_var;                       // BB variable to cnf var
    bool                            has_model;                     // Is the model computed
    Map<PTRef,ValPair,PTRefHash>    model;                         // Model is stored here

    int                             bitwidth;
};

#endif
