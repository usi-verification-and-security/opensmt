/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

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

#ifndef CNFIZER_H
#define CNFIZER_H

#include "Global.h"
#include "Theory.h"
#include "Logic.h"

class SimpSMTSolver;
class CnfState;
class THandler;
class SMTConfig;
class TermMapper;

// A small typechecked class for checkClause type return values to enable us to check whether the formula is unsatisfiable simultaneously
class ckval {
    char value;
    explicit ckval(int v) : value(v) { }
public:
    ckval()          : value(0) { }
    int toInt(void) const { return value; }
    bool operator == (ckval c) const { return value == c.value; }
    bool operator != (ckval c) const { return value == c.value; }

    friend ckval toCkval(int v);
};
inline ckval toCkval(int v) {return ckval(v); }

const ckval ck_True  = toCkval( 1);
const ckval ck_False = toCkval(-1);
const ckval ck_Unsat = toCkval( 0);



//
// Generic class for conversion into CNF
//
class Cnfizer
{
public:
    SimpSMTSolver&      solver;
protected:
    SMTConfig&          config;
    Theory&             theory;
    Logic&              logic;
    TermMapper&         tmap;

    THandler&           thandler;
    bool                s_empty;

public:

    Cnfizer( SMTConfig &    config_
           , Theory&        logic_
           , TermMapper&    tmap_
           , THandler&      thandler_
           , SimpSMTSolver& solver_
           );


    virtual ~Cnfizer( ) { }

    lbool cnfizeAndGiveToSolver (PTRef, FrameId frame_id); // Main routine

    vec<ValPair>* getModel ();                              // Retrieves the model (if SAT and solved)

    lbool  getTermValue(PTRef) const;

    void   initialize      ();
    lbool  solve           (vec<FrameId>& en_frames);

    PTRef  expandItes      (vec<PtChild>&);

    bool  isNPAtom         (PTRef r, PTRef& p)    const; // Check if r is a (negated) atom.  Return true if the corresponding atom is negated.  The purified reference is placed in the second argument.
    bool  solverEmpty      ()                     const { return s_empty; }

    void  getSolverState   (CnfState& cs);
    void  getVarMapping    (CnfState&);
protected:

#ifdef PRODUCE_PROOF
    virtual bool cnfize(PTRef, const ipartitions_t&) = 0;
#else
    virtual bool cnfize                 ( PTRef ) = 0; // Actual cnfization. To be implemented in derived classes
#endif //PRODUCE_PROOF
#ifdef PRODUCE_PROOF
    bool deMorganize(PTRef, const ipartitions_t&);
#else
    bool     deMorganize                ( PTRef );                                    // Apply deMorgan rules whenever feasible
#endif //PRODUCE_PROOF

    PTRef    rewriteMaxArity            ( PTRef, Map<PTRef, int, PTRefHash> & );   // Rewrite terms using maximum arity

public:
    bool     checkClause                ( PTRef ); // Check if a formula is a clause
    bool     checkCnf                   ( PTRef );                            // Check if formula is in CNF
    bool     checkDeMorgan              ( PTRef );                            // Check if formula can be deMorganized
    void     retrieveTopLevelFormulae   ( PTRef, vec<PTRef> & );         // Retrieves the list of top-level formulae
protected:
#ifdef PRODUCE_PROOF
    bool giveToSolver(PTRef, const ipartitions_t &);
#else
    bool     giveToSolver               ( PTRef );                              // Gives formula to the SAT solver
#endif // PRODUCE_PROOF


#ifdef PRODUCE_PROOF
    bool  addClause                  ( const vec<Lit>&, const ipartitions_t& mask = 0);
#else
    bool  addClause                  ( const vec<Lit>& );
#endif

    void  retrieveClause             ( PTRef, vec<PTRef> & );         // Retrieve a clause from a formula
    void  retrieveConjuncts          ( PTRef, vec<PTRef> & );         // Retrieve the list of conjuncts

//  Enode * toggleLit		   ( Enode * );                              // Handy function for toggling literals



private:
    class pi {
      public:
        PTRef x;
        bool done;
        pi(PTRef x_) : x(x_), done(false) {}
    };

    void    computeIncomingEdges (PTRef, Map<PTRef, int, PTRefHash> & );         // Computes the list of incoming edges for a node
    PTRef   mergeEnodeArgs       ( PTRef
                                 , Map<PTRef, PTRef, PTRefHash> &
                                 , Map<PTRef, int, PTRefHash> & );  // Subroutine for rewriteMaxArity

    bool    checkConj            (PTRef); // Check if a formula is a conjunction
    bool    checkPureConj        (PTRef, Map<PTRef,bool,PTRefHash>& check_cache); // Check if a formula is purely a conjuntion


    // The special boolean symbols
protected:

    Map<PTRef,bool,PTRefHash,Equal<PTRef> >   processed;  // Is a term already processed
    Map<PTRef,Var,PTRefHash,Equal<PTRef> >    seen;       // mapping from PTRef to var

    PTRef frame_term;
    vec<PTRef> frame_terms;
    void setFrameTerm(FrameId frame_id);

//    bool  isLit            (PTRef r);
    bool  isBooleanOperator(SymRef tr) { return logic.isBooleanOperator(tr); } // (tr == logic.getSym_and()) | (tr == logic.getSym_or() ) | (tr == logic.getSym_not() ) | (tr == logic.getSym_eq() ) | (tr == logic.getSym_xor() ); }
    bool  isTheorySymbol   (SymRef tr) const { return logic.isTheorySymbol(tr); }
    bool  isIte            (SymRef tr) const { return logic.isIte(tr); }
    bool  isAtom           (PTRef r) const;
    void  declareAtom      (PTRef, SymRef);              // Declare an atom for the smt/sat solver
    bool  termSeen         (PTRef)                const; // True if the term has been seen and thus processed in the sense that there is already literal corresponding to it.  Sees through negations.
};

#endif
