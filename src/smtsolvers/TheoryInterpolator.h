#ifndef THEORY_INTERPOLATOR_H
#define THEORY_INTERPOLATOR_H

#include "PtStore.h"
#include "PartitionManager.h"
#include "OsmtInternalException.h"

#include <memory>
#include <algorithm>

class TermColorInfo {
public:
    virtual icolor_t getColorFor(PTRef term) = 0;
    virtual ~TermColorInfo() = default;

};

class GlobalTermColorInfo : public TermColorInfo {
public:
    GlobalTermColorInfo(PartitionManager & pmanager, ipartitions_t mask) : pmanager(pmanager), mask(std::move(mask)) {}

    icolor_t getColorFor(PTRef term) override {
        auto const & termMask = pmanager.getIPartitions(term);
        auto res = getColorForMask(termMask);
        if (res == icolor_t::I_UNDEF) {
            throw OsmtInternalException("No color detected for term");
        }
        return res;
    }

private:
    PartitionManager & pmanager;
    ipartitions_t mask;

    icolor_t getColorForMask(ipartitions_t const & otherMask) {
        bool isInA = (otherMask & mask) != 0;
        bool isInB = (otherMask & ~mask) != 0;
        if (isInA and not isInB) { return icolor_t::I_A; }
        if (isInB and not isInA) { return icolor_t::I_B; }
        if (isInA and isInB) { return icolor_t::I_AB; }
        return icolor_t::I_UNDEF;
    }
};

/*
 * Stores color information for a set of terms given the colors of top-level term.
 *
 * Terms can be A-local, B-local, or AB-shared.
 * Note: If a term f(x) is local, but both the function symbol and all the arguments are AB-shared,
 *       then f(x) will also be stored as shared.
 */
class LocalTermColorInfo : public TermColorInfo {
public:

    template<typename TMap>
    LocalTermColorInfo(TMap const & topLevelMap, Logic const & logic) {
        termColors[logic.getTerm_true()] = icolor_t::I_AB;
        termColors[logic.getTerm_false()] = icolor_t::I_AB;
        computeColorsForAllSubterms(topLevelMap, logic);
    }

    icolor_t getColorFor(PTRef term) override {
        auto it = termColors.find(term);
        if (it == termColors.end()) {
            throw OsmtInternalException("No color detected for term");
        }
        return it->second;
    }

private:
    std::unordered_map<PTRef, icolor_t, PTRefHash> termColors;

    template<typename TMap>
    void computeColorsForAllSubterms(TMap const & topLevelColors, Logic const & logic) {
        // MB: NOTE! If P(a) is A-local, but both symbols P and a are shared, than P(a) should be shared and not A-local
        using entry_t = std::pair<const PTRef, icolor_t>;
        auto colorUnion = [](icolor_t f, icolor_t s) { return f | s; };
        std::vector<entry_t> queue;
        for (auto entry : topLevelColors) {
            queue.push_back(entry);
        }
        std::unordered_map<SymRef, icolor_t, SymRefHash> symbolColors;
        while (not queue.empty()) {
            auto const entry = queue.back();
            icolor_t colorToAssign = entry.second;
            PTRef term = entry.first;
            queue.pop_back();
            auto it = termColors.find(term);
            if (it != termColors.end()) {
                icolor_t assignedColor = it->second;
                if (assignedColor == colorToAssign || assignedColor == icolor_t::I_AB) { // already processed, color does not change
                    continue;
                } else { // assigning new color
                    assert(assignedColor == icolor_t::I_A or assignedColor == icolor_t::I_B);
                    colorToAssign = colorUnion(colorToAssign, assignedColor);
                    assert(colorToAssign == icolor_t::I_AB);
                }
            }
            // if we reach here, we need to propagate colorToAssign to the whole term subtree of `term`
            termColors[term] = colorToAssign;
            for (PTRef child : logic.getPterm(term)) {
                queue.emplace_back(child, colorToAssign);
            }
            // add symbol information
            auto insertRes = symbolColors.insert(std::make_pair(logic.getSymRef(term), colorToAssign));
            if (not insertRes.second) { // there was entry for this symbol already
                auto entryIt = insertRes.first;
                entryIt->second = colorUnion(entryIt->second, colorToAssign);
            }
        }
        // Make sure complex terms have correct color assigned
        vec<PTRef> terms;
        for (auto const & entry : termColors) {
            PTRef term = entry.first;
            if (entry.second != icolor_t::I_AB and (logic.isUF(term) or logic.isUP(term)) and
                symbolColors.at(logic.getSymRef(term)) == icolor_t::I_AB) {
                terms.push(term);
            }
        }

        sort(terms, [](PTRef p, PTRef q) { return p.x > q.x; }); // to process children before parents

        for (PTRef term : terms) {
            auto & color = termColors.at(term);
            assert(color != icolor_t::I_AB and (logic.isUF(term) or logic.isUP(term)));
            assert(symbolColors.at(logic.getSymRef(term)) == icolor_t::I_AB);
            // if symbol is AB and all children are AB, this term should also be AB
            Pterm const & pterm = logic.getPterm(term);
            bool hasLocalChild = std::any_of(pterm.begin(), pterm.end(),
                                             [this](PTRef child) { return termColors.at(child) != icolor_t::I_AB; });
            if (not hasLocalChild) {
                // everything is AB -> update
                color = icolor_t::I_AB;
            }
        }
    }
};

class TheoryInterpolator
{
public:
    using ItpColorMap = std::map<PTRef, icolor_t>;
    virtual PTRef getInterpolant(const ipartitions_t&, ItpColorMap *, PartitionManager &pmanager) = 0;
};

#endif //THEORY_INTERPOLATOR_H
