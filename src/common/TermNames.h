#ifndef OPENSMT_TERMNAMES_H
#define OPENSMT_TERMNAMES_H

#include "ScopedVector.h"

#include <pterms/PTRef.h>

#include <string>
#include <unordered_map>
#include <vector>

namespace opensmt {
using TermName = std::string;

class TermNames {
public:
    bool contains(TermName const & name) const { return nameToTerm.contains(name); }
    bool contains(PTRef term) const { return termToNames.contains(term); }

    void insert(TermName const & name, PTRef term, bool scoped = false) {
        assert(not contains(name));
        nameToTerm.emplace(name, term);
        termToNames[term].push_back(name);
        if (scoped) { scopedNames.push(name); }
    }

    PTRef termByName(TermName const & name) const {
        assert(contains(name));
        return nameToTerm.at(name);
    }

    std::vector<TermName> const & namesForTerm(PTRef term) const {
        assert(contains(term));
        return termToNames.at(term);
    }

    // Returns any name associated with the term
    TermName const & nameForTerm(PTRef term) const {
        auto & vec = namesForTerm(term);
        assert(not vec.empty());
        return vec.front();
    }

    auto begin() const { return scopedNames.begin(); }
    auto end() const { return scopedNames.end(); }

protected:
    friend class MainSolver;

    void pushScope() { scopedNames.pushScope(); }

    void popScope() {
        scopedNames.popScope([this](TermName const & name) {
            auto it = nameToTerm.find(name);
            if (it == nameToTerm.end()) { return; }
            PTRef term = it->second;
            assert(termToNames.find(term) != termToNames.end());
            auto & names = termToNames.at(term);
            names.erase(std::find(names.begin(), names.end(), name));
            nameToTerm.erase(it);
        });
    }

private:
    using NameToTermMap = std::unordered_map<TermName, PTRef>;
    using TermToNamesMap = std::unordered_map<PTRef, std::vector<TermName>, PTRefHash>;

    ScopedVector<TermName> scopedNames;
    NameToTermMap nameToTerm;
    TermToNamesMap termToNames;
};
} // namespace opensmt

#endif // OPENSMT_TERMNAMES_H
