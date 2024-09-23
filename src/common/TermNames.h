#ifndef OPENSMT_TERMNAMES_H
#define OPENSMT_TERMNAMES_H

#include "ScopedVector.h"

#include <pterms/PTRef.h>

#include <optional>
#include <string>
#include <unordered_map>
#include <vector>

namespace opensmt {
using TermName = std::string;

class TermNames {
public:
    using value_type = pair<TermName const &, PTRef const &>;

    TermNames(SMTConfig const & conf) : config{conf} {}

    bool isGlobal() const { return config.declarations_are_global(); }

    bool contains(TermName const & name) const { return nameToTerm.contains(name); }
    bool contains(PTRef term) const { return termToNames.contains(term); }

    void insert(TermName const & name, PTRef term) {
        assert(not contains(name));
        nameToTerm.emplace(name, term);
        termToNames[term].push_back(name);
        scopedNames.push(name);
        _terms.push_back(term);
        assert(scopedNames.size() == _terms.size());
    }

    PTRef termByName(TermName const & name) const {
        assert(contains(name));
        return nameToTerm.at(name);
    }

    std::vector<TermName> const & namesForTerm(PTRef term) const {
        assert(contains(term));
        return termToNames.at(term);
    }

    // Returns any name from the vector
    static TermName const & pickName(std::vector<TermName> const & vec) {
        assert(not vec.empty());
        return vec.front();
    }

    // Returns any name associated with the term
    TermName const & nameForTerm(PTRef term) const {
        auto & vec = namesForTerm(term);
        return pickName(vec);
    }

    std::optional<PTRef> tryGetTermByName(TermName const & name) const {
        if (auto it = nameToTerm.find(name); it != nameToTerm.end()) { return it->second; }

        return {};
    }

    // std::optional does not work with references so we must use pointers
    std::vector<TermName> const * tryGetNamesForTerm(PTRef term) const {
        if (auto it = termToNames.find(term); it != termToNames.end()) { return &it->second; }

        return nullptr;
    }

    TermName const * tryGetNameForTerm(PTRef term) const {
        if (auto vecPtr = tryGetNamesForTerm(term)) { return &pickName(*vecPtr); }

        return nullptr;
    }

    // Iterates over const names and their corresponding terms (according to value_type)
    inline auto begin() const noexcept;
    inline auto end() const noexcept;

    bool empty() const noexcept { return scopedNames.empty(); }
    std::size_t size() const noexcept { return scopedNames.size(); }

    // A const view to just the terms
    auto const & terms() const { return _terms; }

protected:
    friend class MainSolver;

    using NameToTermMap = std::unordered_map<TermName, PTRef>;
    using TermToNamesMap = std::unordered_map<PTRef, std::vector<TermName>, PTRefHash>;

    class Iterator {
    public:
        using NameIterator = ScopedVector<TermName>::const_iterator;
        using TermIterator = std::vector<PTRef>::const_iterator;

        explicit Iterator(NameIterator nit, TermIterator tit) : nameIterator{nit}, termIterator{tit} {}

        value_type operator*() const { return {*nameIterator, *termIterator}; }

        Iterator & operator++() {
            ++nameIterator;
            ++termIterator;
            return *this;
        }
        Iterator operator++(int) {
            auto it = *this;
            operator++();
            return it;
        }

        bool operator==(Iterator const & rhs) const noexcept { return nameIterator == rhs.nameIterator; }

    protected:
        NameIterator nameIterator;
        TermIterator termIterator;
    };

    void pushScope() {
        if (isGlobal()) { return; }
        scopedNames.pushScope();
    }

    void popScope() {
        if (isGlobal()) { return; }
        assert(scopedNames.size() == _terms.size());
        scopedNames.popScope([this](TermName const & name) {
            auto it = nameToTerm.find(name);
            if (it == nameToTerm.end()) { return; }
            PTRef term = it->second;
            auto & names_ = const_cast<std::vector<TermName> &>(namesForTerm(term));
            names_.erase(std::find(names_.begin(), names_.end(), name));
            nameToTerm.erase(it);
        });
        assert(scopedNames.size() <= _terms.size());
        _terms.resize(scopedNames.size());
    }

    SMTConfig const & config;

    ScopedVector<TermName> scopedNames;
    NameToTermMap nameToTerm;
    TermToNamesMap termToNames;

    std::vector<PTRef> _terms;
};

auto TermNames::begin() const noexcept {
    return Iterator{scopedNames.begin(), _terms.begin()};
}

auto TermNames::end() const noexcept {
    return Iterator{scopedNames.end(), _terms.end()};
}
} // namespace opensmt

#endif // OPENSMT_TERMNAMES_H
