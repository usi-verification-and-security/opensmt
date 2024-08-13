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

#include "TermMapper.h"

#include <api/PartitionManager.h>
#include <logics/Logic.h>
#include <logics/Theory.h>

#include <unordered_set>

namespace opensmt {
class SimpSMTSolver;
class THandler;
struct SMTConfig;

//
// Generic class for conversion into CNF
//
class Cnfizer {
public:
    using FrameId = uint32_t;

    struct ClauseCallBack {
        virtual void operator()(vec<Lit> &&) = 0;
    };

    Cnfizer(Logic & logic, TermMapper & tmap);

    virtual ~Cnfizer() = default;
    Cnfizer(Cnfizer const &) = delete;
    Cnfizer & operator=(Cnfizer const &) = delete;
    Cnfizer(Cnfizer &&) = default;
    Cnfizer & operator=(Cnfizer &&) = delete;

    void cnfize(PTRef, FrameId frame_id);

    void setClauseCallBack(ClauseCallBack * callback) {
        assert(callback);
        this->clauseCallBack = callback;
    }

protected:
    class Cache {
    public:
        Cache() = default;
        bool contains(PTRef term, FrameId frame);
        void insert(PTRef term, FrameId frame);

    private:
        using CacheEntry = std::pair<PTRef, FrameId>;

        struct EntryHash {
            std::size_t operator()(CacheEntry entry) const {
                std::hash<uint32_t> hasher;
                return (hasher(entry.first.x) ^ hasher(entry.second));
            }
        };

        FrameId baseFrame = 0;
        std::unordered_set<CacheEntry, EntryHash> cache;
    };

    virtual void cnfize(PTRef) = 0; // Actual cnfization. To be implemented in derived classes
    void cnfizeAndAssert(PTRef);    // Cnfize and assert the top-level.

    bool isClause(PTRef);
    bool checkDeMorgan(PTRef);
    void processClause(PTRef f);
    void addClause(vec<Lit> &&);
    void deMorganize(PTRef);

    void retrieveClause(PTRef, vec<Lit> &);
    void retrieveConjuncts(PTRef, vec<PTRef> &); // Retrieve the list of conjuncts

    bool isLiteral(PTRef ptr) const;
    inline Lit getOrCreateLiteralFor(PTRef ptr) { return this->tmap.getOrCreateLit(ptr); }

    Logic & logic;
    TermMapper & tmap;
    Cache alreadyProcessed;
    ClauseCallBack * clauseCallBack;

    FrameId currentFrameId = 0;

private:
    // Check if a formula is purely a conjunction
    bool checkPureConj(PTRef, Map<PTRef, bool, PTRefHash> & check_cache);
};
} // namespace opensmt

#endif
