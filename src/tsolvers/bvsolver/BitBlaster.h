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

#include "BVStore.h"

#include <smtsolvers/SimpSMTSolver.h>

#include <unordered_map>

namespace opensmt {

// forward declarations
class BVLogic;
class MainSolver;
class Enode;

class BitBlaster
{
public:
    BitBlaster(SolverId, SMTConfig & c, MainSolver & mainSolver, BVLogic & bvlogic, vec<PtAsgn> & ex,
               vec<PTRef> & s);
    ~BitBlaster ( );

    lbool inform             (PTRef); // For the interface for bitvector solver
    lbool check              ( );
    bool  assertLit          (PtAsgn);

    lbool insertEq           (PTRef tr, BVRef& out); // For the interface for theory refinement
    lbool insertOr           (PTRef tr, BVRef& out); // For the interface for theory refinement

    void pushBacktrackPoint  ( );
    void popBacktrackPoint   ( );

    void    computeModel     ( );
    PTRef   getValue         (PTRef tr) const { if (has_model) { return model.at(tr); } else { return PTRef_Undef; }}

    // Public Theory refinement stuff
    lbool notifyEqualities   (); // Check all refined equalities, add explicit new terms for them
    void  bindCUFToBV        (PTRef cuf_tr, PTRef bv_tr) { assert(!pToB.has(cuf_tr)); bbTerm(bv_tr); pToB.insert(cuf_tr, bv_tr); refined.push(cuf_tr); }
    PTRef mkCollate32        (vec<PTRef>& bits);
    PTRef mkExtract          (PTRef tr, int i);
    // Theory refinement stuff
    PTRef                      getBoundPTRef (PTRef tr) { assert(pToB.has(tr)); return pToB[tr]; }
    bool                       isBound       (PTRef tr) { return pToB.has(tr); }
private:
    Map<PTRef,PTRef,PTRefHash> pToB;
    vec<PTRef>                 refined;
    int                        last_refined;
    lbool                      notifyEquality(PTRef tr_eq);

    // -----
    BVRef bbTerm             (PTRef);
    lbool insert             (PTRef tr, BVRef& out); // The unsafe interface for theory refinement
    BVRef          updateCache  (PTRef tr);
    SMTConfig &    config;                        // Configuration
    MainSolver&    mainSolver;
    BVLogic&       logic;                         // Egraph store
    THandler&      thandler;
    SimpSMTSolver& solverP;                       // Solver with proof logger

    bool addClause(vec<Lit> && c);

    static const char* s_bbEq;
    static const char* s_bbAnd;
    static const char* s_bbBvslt;
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
    static const char* s_bbBvcarry;
    static const char* s_bbBvlsh;
    static const char* s_bbBvlrsh;
    static const char* s_bbBvarsh;

    char* getName(const char* base) const;
    void  getBVVars(const char* base, vec<PTRef>& vars, int width);
    PTRef mkActVar(const char* base);
    // Predicates
    BVRef bbEq         (PTRef);
    BVRef bbBvslt      (PTRef);
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
    BVRef bbBvlshift   (PTRef);
    BVRef bbBvrshift   (PTRef, bool);
    BVRef bbBvlrshift  (PTRef);
    BVRef bbBvarshift  (PTRef);
    BVRef bbSignExtend (PTRef);
    BVRef bbVar        (PTRef);
    BVRef bbConstant   (PTRef);
    BVRef bbDistinct   (PTRef);

    PTRef bbBvadd_carryonly(PTRef sum, PTRef cin); // for signed comparison
    void ls_write(int s, int i, PTRef tr, std::vector<vec<PTRef> >& table); // Helper function for shifts
    PTRef ls_read(int s, int i, std::vector<vec<PTRef> >& table); // Helper function for shifts

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

    std::vector< Lit >                   cnf_cache;                     // Global cache for cnfizer
    std::vector< Var >                   enode_id_to_var;               // Theory atom to Minisat Var correspondence
    std::vector< Enode * >               var_to_enode;                  // Minisat Var to Theory Atom correspondence


    vec<PtAsgn> &                   explanation;                   // Reference to explanation
    vec<PTRef> &                    suggestions;                   // Reference to suggestions

    vec<PTRef>                      variables;                     // Variables
    std::map< int, Var >                 cnf_var;                       // BB variable to cnf var
    bool                            has_model;                     // Is the model computed
    std::unordered_map<PTRef,PTRef,PTRefHash>    model;          // Model is stored here

    int                             bitwidth;
};

}

#endif
