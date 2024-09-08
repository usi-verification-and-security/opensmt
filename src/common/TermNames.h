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
    TermNames(SMTConfig const & conf) : config{conf} {}

    bool isGlobal() const { return config.declarations_are_global(); }

    bool contains(TermName const & name) const { return nameToTerm.contains(name); }
    bool contains(PTRef term) const { return termToNames.contains(term); }

    void insert(TermName const & name, PTRef term) {
        assert(not contains(name));
        nameToTerm.emplace(name, term);
        termToNames[term].push_back(name);
        names.push(name);
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

    auto begin() const noexcept { return names.begin(); }
    auto end() const noexcept { return names.end(); }

    bool empty() const noexcept { return size() == 0; }
    std::size_t size() const noexcept { return names.size(); }

protected:
    friend class MainSolver;

    using NameToTermMap = std::unordered_map<TermName, PTRef>;
    using TermToNamesMap = std::unordered_map<PTRef, std::vector<TermName>, PTRefHash>;

    void pushScope() {
        if (isGlobal()) { return; }
        names.pushScope();
    }

    void popScope() {
        if (isGlobal()) { return; }
        names.popScope([this](TermName const & name) {
            auto it = nameToTerm.find(name);
            if (it == nameToTerm.end()) { return; }
            PTRef term = it->second;
            assert(termToNames.find(term) != termToNames.end());
            auto & names = termToNames.at(term);
            names.erase(std::find(names.begin(), names.end(), name));
            nameToTerm.erase(it);
        });
    }

    SMTConfig const & config;

    ScopedVector<TermName> names;
    NameToTermMap nameToTerm;
    TermToNamesMap termToNames;
};
} // namespace opensmt

#endif // OPENSMT_TERMNAMES_H
