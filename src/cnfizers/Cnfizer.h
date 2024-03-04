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
    struct ClauseCallBack {
        virtual void operator()(vec<Lit> &&) = 0;
    };
protected:
    using FrameId = uint32_t;

    class Cache {
        using CacheEntry = std::pair<PTRef, FrameId>;

        struct EntryHash {
            std::size_t operator () (CacheEntry entry) const {
                std::hash<uint32_t> hasher;
                return (hasher(entry.first.x) ^ hasher(entry.second));
            }
        };

        FrameId baseFrame = 0;
        std::unordered_set<CacheEntry, EntryHash> cache;
    public:
        Cache() = default;
        bool contains(PTRef term, FrameId frame);
        void insert(PTRef term, FrameId frame);
    };

    Logic & logic;
    TermMapper & tmap;
    Cache alreadyProcessed;
    ClauseCallBack * clauseCallBack;


public:

    Cnfizer(Logic & logic, TermMapper & tmap);

    virtual ~Cnfizer() = default;
    Cnfizer             (const Cnfizer&) = delete;
    Cnfizer& operator = (const Cnfizer&) = delete;
    Cnfizer             (Cnfizer&&) = default;
    Cnfizer& operator = (Cnfizer&&) = delete;

    void cnfize(PTRef, FrameId frame_id);

    void setClauseCallBack(ClauseCallBack * callback) { assert(callback); this->clauseCallBack = callback; }

protected:
    virtual void cnfize(PTRef) = 0; // Actual cnfization. To be implemented in derived classes
    void cnfizeAndAssert(PTRef);    // Cnfize and assert the top-level.

    bool isClause(PTRef);
    bool checkDeMorgan(PTRef);
    void processClause(PTRef f);
    void addClause(vec<Lit> &&);
    void deMorganize(PTRef);

    void retrieveClause(PTRef, vec<Lit> &);
    void retrieveConjuncts(PTRef, vec<PTRef> &); // Retrieve the list of conjuncts

private:
    bool checkPureConj(PTRef, Map<PTRef, bool, PTRefHash> & check_cache); // Check if a formula is purely a conjuntion

protected:
    bool isLiteral(PTRef ptr) const;
    inline Lit getOrCreateLiteralFor(PTRef ptr) {return this->tmap.getOrCreateLit(ptr);}

    FrameId currentFrameId = 0;
};

#endif
