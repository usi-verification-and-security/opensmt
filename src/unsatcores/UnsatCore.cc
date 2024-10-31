#include "UnsatCore.h"

#include <common/TermNames.h>
#include <logics/Logic.h>

#include <iostream>

namespace opensmt {

void UnsatCore::print() const {
    print(std::cout);
}

void UnsatCore::print(std::ostream & os) const {
    printBegin(os);
    printBody(os);
    printEnd(os);
}

void UnsatCore::printBegin(std::ostream & os) const {
    os << "(\n";
}

void UnsatCore::printBody(std::ostream & os) const {
    for (PTRef term : getTerms()) {
        printTerm(os, term);
        os << '\n';
    }
}

void UnsatCore::printEnd(std::ostream & os) const {
    os << ')' << std::endl;
}

void NamedUnsatCore::printTerm(std::ostream & os, PTRef term) const {
    assert(termNames.contains(term));
    os << termNames.nameForTerm(term);
}

void FullUnsatCore::printTerm(std::ostream & os, PTRef term) const {
    os << logic.printTerm(term);
}

} // namespace opensmt
