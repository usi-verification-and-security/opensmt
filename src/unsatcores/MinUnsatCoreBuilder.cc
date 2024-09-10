
#include "MinUnsatCoreBuilder.h"

#include <api/MainSolver.h>

namespace opensmt {

std::unique_ptr<UnsatCore> MinUnsatCoreBuilder::build() {
    buildBody();
    return buildReturn();
}

void MinUnsatCoreBuilder::buildBody() {
    UnsatCoreBuilder::buildBody();
    minimize();
}

void MinUnsatCoreBuilder::minimize() {
    minimizeInit();
    minimizeAlg();
    minimizeFinish();
}

void MinUnsatCoreBuilder::minimizeInit() {
    assert(terms.size() >= namedTerms.size());
    assert(size_t(namedTerms.size()) == namedTermsIdxs.size());
}

void MinUnsatCoreBuilder::minimizeAlgNaive() {
    if (namedTerms.size() == 0) return;

    auto const namedTermsIdxsEnd = namedTermsIdxs.end();
    auto const isNamedTerm = [namedTermsIdxsEnd](size_t idx, auto namedTermsIdxsIt) {
        if (namedTermsIdxsIt == namedTermsIdxsEnd) { return false; }
        assert(idx <= *namedTermsIdxsIt);
        return (idx == *namedTermsIdxsIt);
    };
    decltype(terms) newTerms;
    size_t const termsSize = terms.size();
    for (auto [idx, namedTermsIdxsIt] = std::tuple{size_t{0}, namedTermsIdxs.begin()}; idx < termsSize; ++idx) {
        if (isNamedTerm(idx, namedTermsIdxsIt)) {
            ++namedTermsIdxsIt;
            continue;
        }
        PTRef term = terms[idx];
        smtSolverPtr->insertFormula(term);
        newTerms.push(term);
    }

    decltype(terms) newNamedTerms;
    size_t const namedTermsSize = namedTerms.size();
    for (size_t namedIdx = 0; namedIdx < namedTermsSize; ++namedIdx) {
        smtSolverPtr->push();

        // try to ignore namedTerms[namedIdx]

        for (size_t keptNamedIdx = namedIdx + 1; keptNamedIdx < namedTermsSize; ++keptNamedIdx) {
            PTRef term = namedTerms[keptNamedIdx];
            smtSolverPtr->insertFormula(term);
        }

        sstat const res = smtSolverPtr->check();
        assert(res == s_True || res == s_False);
        bool const isRedundant = (res == s_False);

        smtSolverPtr->pop();

        if (isRedundant) continue;

        // namedTerms[namedIdx] is not redundant - include it

        PTRef term = namedTerms[namedIdx];
        smtSolverPtr->insertFormula(term);
        newTerms.push(term);
        newNamedTerms.push(term);
    }

    terms = std::move(newTerms);
    namedTerms = std::move(newNamedTerms);
}

} // namespace opensmt
