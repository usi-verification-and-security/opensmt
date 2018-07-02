//
// Created by Martin Blicha on 01.04.18.
//

#include <Real.h>
#include "LARefs.h"
#include "Polynomial.h"

void Polynomial::addTerm(LVRef var, opensmt::Real coeff) {
    assert(poly.find(var) == poly.end());
    poly[var] = std::move(coeff);
}

unsigned long Polynomial::size() const {
    return poly.size();
}

const FastRational &Polynomial::getCoeff(LVRef var) const {
    return poly.at(var);
}

void Polynomial::removeVar(LVRef var) {
    assert(poly.find(var) != poly.end());
    poly.erase(var);
}

void Polynomial::negate() {
    for(auto & term : poly) {
        term.second.negate();
    }
}

void Polynomial::divideBy(const opensmt::Real &r) {
    for(auto & term : poly) {
        term.second /= r;
    }
}

MergeResult
Polynomial::merge(const Polynomial &other, const opensmt::Real &coeff) {
    MergeResult res;
    auto & added = res.added;
    auto & removed = res.removed;
    for(const auto & term : other) {
        auto var = term.first;
        auto var_coeff = term.second;
        auto var_in_current = poly.find(var);
        if(var_in_current == poly.end()) {
            // not present before
            added.push_back(var);
            this->addTerm(var, coeff * var_coeff);
        }
        else{
            // present, sum up coeffs
            var_in_current->second += coeff * var_coeff;
            if(var_in_current->second.isZero()){
                removed.push_back(var);
                this->removeVar(var);
            }
        }
    }
    return res;
}
