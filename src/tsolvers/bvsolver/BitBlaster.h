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

class BitBlaster
{
public:

    BitBlaster ( SolverId
               , SMTConfig &
               , MainSolver&
               , vec<PtAsgn> &
               , vec<DedElem> &
               , vec<PTRef> & );
    ~BitBlaster ( );

    lbool inform             (PTRef);
    lbool check              ( );
    bool  assertLit          (PtAsgn);

    void pushBacktrackPoint  ( );
    void popBacktrackPoint   ( );

    void computeModel        ( );
    Real getValue            (PTRef);
private:
    vec<PTRef>&    updateCache  (PTRef tr);
    vec<PTRef>     ptref_vec_empty;
    SMTConfig &    config;                        // Configuration
    MainSolver&    mainSolver;
    Logic&         logic;                         // Egraph store
    THandler&      thandler;
    SimpSMTSolver& solverP;                       // Solver with proof logger

    bool addClause ( vec< Lit > &, PTRef );

public:
    vec<PTRef> & bbTerm       (PTRef);
    // Predicates
    vec<PTRef> & bbEq         (PTRef);
    vec<PTRef> & bbBvsle      (PTRef);
    vec<PTRef> & bbBvule      (PTRef);
    // Terms
    vec<PTRef> & bbConcat     (PTRef);
    vec<PTRef> & bbExtract    (PTRef);
    vec<PTRef> & bbBvand      (PTRef);
    vec<PTRef> & bbBvor       (PTRef);
    vec<PTRef> & bbBvxor      (PTRef);
    vec<PTRef> & bbBvnot      (PTRef);
    vec<PTRef> & bbBvadd      (PTRef);
    vec<PTRef> & bbBvmul      (PTRef);
    vec<PTRef> & bbBvudiv     (PTRef);
    vec<PTRef> & bbBvurem     (PTRef);
    vec<PTRef> & bbSignExtend (PTRef);
    vec<PTRef> & bbVar        (PTRef);
    vec<PTRef> & bbConstant   (PTRef);
    vec<PTRef> & bbDistinct   (PTRef);
  // Not yet considered
  // vector< Enode * > & bbUf         ( Enode * );
  // vector< Enode * > & bbUp         ( Enode * );

private:

    void     cleanGarbage          ( );                            // Clean garbage on demand

    PTRef    simplify              ( PTRef );                    // Further simplifications
//    Enode *  rewriteMaxArity       ( Enode *
//                                   , map< int, int > & );
//    void     computeIncomingEdges  ( Enode *
//                                    , map< int, int > & );          // Computes the list of incoming edges for a node
    Enode *  mergeEnodeArgs        ( Enode *
                                    , map< int, Enode * > &
                                    , map< int, int > & );          // Rewrite terms using maximum arity

    Lit                             constTrue;                     // Constant literal set to true
    Lit                             constFalse;                    // Constant literal set to false

    vector< vec<PTRef> * >          bb_cache;                      // Global cache for bitblasting
    vector< Lit >                   cnf_cache;                     // Global cache for cnfizer
    vector< Var >                   enode_id_to_var;               // Theory atom to Minisat Var correspondence
    vector< Enode * >               var_to_enode;                  // Minisat Var to Theory Atom correspondence


    vec<PtAsgn> &                   explanation;                   // Reference to explanation
    vec<DedElem> &                  deductions;                    // Reference to deductions
    vec<PTRef> &                    suggestions;                   // Reference to suggestions
    vector< vec<PTRef> * >          garbage;                       // Collect for removal

    vec<PTRef>                      variables;                     // Variables
    map< int, Var >                 cnf_var;                       // BB variable to cnf var
    bool                            has_model;                     // Is the model computed
    Map<PTRef,Real,PTRefHash>       model;                         // Model is stored here
};

#endif
