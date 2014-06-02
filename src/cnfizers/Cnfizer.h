/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#ifndef CNFIZER_H
#define CNFIZER_H

#include "TermMapper.h"
#include "Global.h"
//#include "Otl.h"
//#include "SMTSolver.h"
#include "SimpSMTSolver.h"
#include "Egraph.h"
#include "THandler.h"
#include "PtStore.h"
#include "SStore.h"
#include "Logic.h"

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

class ValPair {
  private:
    PTRef       t;
    lbool       v;
  public:
    ValPair(PTRef term, lbool value) : t(term), v(value) {}
    PTRef getTerm()       const { return t; }
    lbool getVal ()       const { return v; }
};

//
// Generic class for conversion into CNF
//
class Cnfizer
{
protected:
    PtStore&            ptstore;         // Reference to the term store
    SMTConfig&          config;
    SymStore&           symstore;
    SStore &            sstore;
    Logic&              logic;
    TermMapper&         tmap;            // Map vars to proper terms

    THandler&           thandler;
    SimpSMTSolver&      solver;
    bool                s_empty;
//    Egraph              uf_solver;

public:

    Cnfizer( PtStore &      ptstore_
           , SMTConfig &    config_
           , SymStore&      symstore_
           , SStore &       sstore_
           , Logic&         logic_
           , TermMapper&    tmap_
           , THandler&      thandler_
           , SimpSMTSolver& solver_
           );


    virtual ~Cnfizer( ) { }

    lbool cnfizeAndGiveToSolver ( PTRef
#ifdef PRODUCE_PROOF
                                , const ipartitions_t = 0
#endif
                                ); // Main routine
    lbool extEquals             ( PTRef new_r, PTRef old_r ); // Tell the solver that two terms are equal (used when equality deduced by a theory solver)

    vec<ValPair>* getModel ();                              // Retrieves the model (if SAT and solved)

    lbool  getTermValue(PTRef);

    void   initialize      ();
    lbool  solve           () { status = solver.solve(); return status; }

    void   crashTest       (int rounds) { solver.crashTest(rounds, tmap.getVar(logic.getTerm_true()), tmap.getVar(logic.getTerm_false())); }
    lbool  getStatus       () { return status; }

    PTRef  expandItes      (vec<PtChild>&);

    void  purify           (PTRef r, PTRef& p, lbool& sgn) const
        {p = r; sgn = l_True; while (ptstore[p].symb() == logic.getSym_not()) { sgn = sgn^1; p = ptstore[p][0]; };}
    bool  isNPAtom         (PTRef r, PTRef& p)    const; // Check if r is a (negated) atom.  Return true if the corresponding atom is negated.  The purified reference is placed in the second argument.
    bool  solverEmpty      ()                     const { return s_empty; }

protected:

#ifdef ENABLE_SHARING_BUG
    // My theory is that the other hash is not used.
    virtual bool cnfize                 (PTRef, Map<PTRef, PTRef, PTRefHash>& valdupmap) = 0;
#else
    virtual bool cnfize                 ( PTRef
#ifdef PRODUCE_PROOF
                                        , const ipartitions_t = 0
#endif
                                        ) = 0; // Actual cnfization. To be implemented in derived classes
#endif
    bool     deMorganize                ( PTRef
#ifdef PRODUCE_PROOF
                                        , const ipartitions_t &
#endif
                                        );                                    // Apply deMorgan rules whenever feasible
    PTRef    rewriteMaxArity            ( PTRef, Map<PTRef, int, PTRefHash> & );   // Rewrite terms using maximum arity

public:
    bool     checkClause                ( PTRef ); // Check if a formula is a clause
    bool     checkCnf                   ( PTRef );                            // Check if formula is in CNF
    bool     checkDeMorgan              ( PTRef );                            // Check if formula can be deMorganized
    void     retrieveTopLevelFormulae   ( PTRef, vec<PTRef> & );         // Retrieves the list of top-level formulae
protected:
    bool     giveToSolver               ( PTRef
#ifdef PRODUCE_PROOF
                                        , const ipartitions_t &
#endif
                                        );                              // Gives formula to the SAT solver


#ifdef PRODUCE_PROOF
    bool  addClause                  ( vec<Lit>&, const ipartitions_t& );
#else
    bool  addClause                  ( vec<Lit>& );
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

    lbool   status;     // The status of the last solver call (initially l_Undef)

    // The special boolean symbols
protected:

    Map<PTRef,bool,PTRefHash,Equal<PTRef> >   processed;  // Is a term already processed
    Map<PTRef,Var,PTRefHash,Equal<PTRef> >    seen;       // mapping from PTRef to var

//    bool  isLit            (PTRef r);
    const Lit findLit      (PTRef ptr);
    bool  isBooleanOperator(SymRef tr) { return logic.isBooleanOperator(tr); } // (tr == logic.getSym_and()) | (tr == logic.getSym_or() ) | (tr == logic.getSym_not() ) | (tr == logic.getSym_eq() ) | (tr == logic.getSym_xor() ); }
    bool  isTheorySymbol   (SymRef tr) const { return logic.isTheorySymbol(tr); }
    bool  isIte            (SymRef tr) const { return logic.isIte(tr); }
    bool  isAtom           (PTRef r) const;
    void  declareAtom      (PTRef, SymRef);              // Declare an atom for the smt/sat solver
    bool  termSeen         (PTRef)                const; // True if the term has been seen and thus processed in the sense that there is already literal corresponding to it.  Sees through negations.

};

#endif
