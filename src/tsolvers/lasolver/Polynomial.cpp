//
// Created by Martin Blicha on 01.04.18.
//

#include <Real.h>
#include "LARefs.h"
#include "Polynomial.h"
#include <iostream>

void Polynomial::addTerm(LVRef var, opensmt::Real coeff) {
    assert(!contains(var));
    Term term {var, std::move(coeff)};
    auto it = std::upper_bound(poly.begin(), poly.end(), term, TermCmp{});
    poly.insert(it, std::move(term));
}

unsigned long Polynomial::size() const {
    return poly.size();
}

const FastRational &Polynomial::getCoeff(LVRef var) const {
    assert(contains(var));
    return findTermForVar(var)->coeff;
}

opensmt::Real Polynomial::removeVar(LVRef var) {
    assert(contains(var));
    iterator it = findTermForVar(var);
    auto coeff = std::move(it->coeff);
    poly.erase(it);
    return coeff;
}

void Polynomial::negate() {
    for(auto & term : poly) {
        term.coeff.negate();
    }
}

void Polynomial::divideBy(const opensmt::Real &r) {
    for(auto & term : poly) {
        term.coeff /= r;
    }
}

void Polynomial::print() const {
    for (auto & term : poly) {
        std::cout << term.coeff << " * " << term.var.x << "v + ";
    }
    std::cout << std::endl;
}