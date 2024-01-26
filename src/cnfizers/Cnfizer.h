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

#include "Theory.h"
#include "Logic.h"
#include "PartitionManager.h"
#include "TermMapper.h"

#include <unordered_set>

class SimpSMTSolver;
class THandler;
struct SMTConfig;

//
// Generic class for conversion into CNF
//
class Cnfizer
{
public:
    SimpSMTSolver&      solver;
protected:
    SMTConfig&          config;
    Logic&              logic;
    PartitionManager&   pmanager;
    TermMapper&         tmap;
    bool                s_empty;

    class Cache {
        PTRef zeroLevelTerm;
        using CacheEntry = std::pair<PTRef, PTRef>;
        std::unordered_set<CacheEntry, PTRefPairHash > cache;
    public:
        Cache(PTRef zeroLevelTerm): zeroLevelTerm(zeroLevelTerm) {}
        bool contains(PTRef term, PTRef frame_term);
        void insert(PTRef term, PTRef frame_term);
    };

    Cache alreadyAsserted;

public:

    Cnfizer( SMTConfig &    config_
           , Logic&        logic_
           , PartitionManager& pmanager_
           , TermMapper&    tmap_
           , SimpSMTSolver& solver_
           );


    virtual ~Cnfizer() = default;
    Cnfizer             (const Cnfizer&) = delete;
    Cnfizer& operator = (const Cnfizer&) = delete;
    Cnfizer             (Cnfizer&&) = default;
    Cnfizer& operator = (Cnfizer&&) = delete;

    lbool cnfizeAndGiveToSolver (PTRef, FrameId frame_id); // Main routine

    lbool  getTermValue(PTRef) const;

    void   initialize      ();
    lbool  solve           (vec<FrameId>& en_frames);

    bool  solverEmpty      ()                     const { return s_empty; }

protected:

    virtual bool cnfizeAndAssert        ( PTRef );       // Cnfize and assert the top-level.
    virtual bool cnfize                 ( PTRef ) = 0;   // Actual cnfization. To be implemented in derived classes
    bool     deMorganize                ( PTRef );       // Apply deMorgan rules whenever feasible
    void     declareVars                (vec<PTRef>&);   // Declare a set of Boolean atoms to the solver (without asserting them)

public:
    bool     isClause                   (PTRef);
    bool     isCnf                      (PTRef);
    bool     checkDeMorgan              ( PTRef );                      // Check if formula can be deMorganized
protected:

    bool     assertClause               (PTRef f);                              // Gives formula to the SAT solver


    bool addClause(const vec<Lit> &);

    void  retrieveClause             ( PTRef, vec<PTRef> & );         // Retrieve a clause from a formula
    void  retrieveConjuncts          ( PTRef, vec<PTRef> & );         // Retrieve the list of conjuncts

private:

    bool    isConjunctionOfClauses (PTRef);
    bool    checkPureConj        (PTRef, Map<PTRef,bool,PTRefHash>& check_cache); // Check if a formula is purely a conjuntion

protected:
    bool isLiteral(PTRef ptr) const;
    inline Lit getOrCreateLiteralFor(PTRef ptr) {return this->tmap.getOrCreateLit(ptr);}
    inline vec<PTRef> getNestedBoolRoots(PTRef ptr) { return logic.getNestedBoolRoots(ptr); }

    bool keepPartitionInfo() const { return config.produce_inter(); }

    int currentPartition = -1;

    vec<PTRef> frame_terms;
    PTRef current_frame_term;
    void setFrameTerm(FrameId frame_id);
};

#endif
