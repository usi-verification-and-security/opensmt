#ifndef OPENSMT_TERMNAMES_H
#define OPENSMT_TERMNAMES_H

#include "ScopedVector.h"
#include "TypeUtils.h"

#include <options/SMTConfig.h>
#include <pterms/PTRef.h>

#include <algorithm>
#include <optional>
#include <string>
#include <type_traits>
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

    [[deprecated("Use tryInsert")]]
    void insert(TermName const & name, PTRef term) {
        assert(not contains(name));
        [[maybe_unused]] bool const success = tryInsert(name, term);
        assert(success);
    }

    bool tryInsert(TermName const & name, PTRef term) {
        auto const [_, inserted] = nameToTerm.try_emplace(name, term);
        if (not inserted) { return false; }

        termToNames[term].push_back(name);
        scopedNamesAndTerms.push({name, term});
        return true;
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

        return std::nullopt;
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

    auto begin() const noexcept { return scopedNamesAndTerms.begin(); }
    auto end() const noexcept { return scopedNamesAndTerms.end(); }

    bool empty() const noexcept { return scopedNamesAndTerms.empty(); }
    std::size_t size() const noexcept { return scopedNamesAndTerms.size(); }

    // A const view to just the names
    inline auto names() const;
    // A const view to just the terms
    inline auto terms() const;

protected:
    friend class MainSolver;

    using ScopedNamesAndTerms = ScopedVector<pair<TermName, PTRef>>;
    using NameToTermMap = std::unordered_map<TermName, PTRef>;
    using TermToNamesMap = std::unordered_map<PTRef, std::vector<TermName>, PTRefHash>;

    template<bool namesView>
    class NamesOrTermsView;
    using NamesView = NamesOrTermsView<true>;
    using TermsView = NamesOrTermsView<false>;

    // avoid undesired overload resolution with the public `namesForTerm`
    std::vector<TermName> & _namesForTerm(PTRef term) const {
        // this is a legal use-case of `const_cast`
        return const_cast<std::vector<TermName> &>(namesForTerm(term));
    }

    void pushScope() {
        if (isGlobal()) { return; }
        scopedNamesAndTerms.pushScope();
    }

    void popScope() {
        if (isGlobal()) { return; }
        scopedNamesAndTerms.popScope([this](auto const & p) {
            auto const & [name, term] = p;
            assert(not contains(term) or nameToTerm.find(name)->second.x == term.x);
            eraseTermName(name);
        });
    }

    bool eraseTermName(TermName const & name) {
        auto termIt = nameToTerm.find(name);
        if (termIt == nameToTerm.end()) { return false; }

        auto const & term = termIt->second;
        auto & names_ = _namesForTerm(term);
        names_.erase(std::find(names_.begin(), names_.end(), name));
        nameToTerm.erase(termIt);
        return true;
    }

    SMTConfig const & config;

    ScopedNamesAndTerms scopedNamesAndTerms;
    NameToTermMap nameToTerm;
    TermToNamesMap termToNames;
};

template<bool namesView>
class TermNames::NamesOrTermsView {
public:
    explicit NamesOrTermsView(TermNames const & termNames_) : termNames{termNames_} {}

    class Iterator {
    public:
        using PairIterator = ScopedNamesAndTerms::const_iterator;

        using Value = std::conditional_t<namesView, TermName const &, PTRef>;

        explicit Iterator(PairIterator pit) : pairIterator{pit} {}

        Value operator*() const {
            if constexpr (namesView) {
                return pairIterator->first;
            } else {
                return pairIterator->second;
            }
        }

        Iterator & operator++() {
            ++pairIterator;
            return *this;
        }
        Iterator operator++(int) {
            auto it = *this;
            operator++();
            return it;
        }

        bool operator==(Iterator const &) const = default;

    protected:
        PairIterator pairIterator;
    };

    auto begin() const noexcept { return Iterator{termNames.scopedNamesAndTerms.begin()}; }
    auto end() const noexcept { return Iterator{termNames.scopedNamesAndTerms.end()}; }

    bool empty() const noexcept { return termNames.scopedNamesAndTerms.empty(); }
    std::size_t size() const noexcept { return termNames.scopedNamesAndTerms.size(); }

protected:
    TermNames const & termNames;
};

auto TermNames::names() const {
    return NamesView(*this);
}

auto TermNames::terms() const {
    return TermsView(*this);
}
} // namespace opensmt

#endif // OPENSMT_TERMNAMES_H
