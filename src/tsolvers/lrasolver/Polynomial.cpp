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
    auto it = findTermForVar(var);
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


MergeResult
Polynomial::merge(const Polynomial &other, const opensmt::Real &coeff) {
    MergeResult res{other.size(), this->size()};
    auto & added = res.added;
    auto & removed = res.removed;
    decltype(poly) merged;
    merged.reserve(std::max(this->poly.size(),other.poly.size()));
    auto myIt = poly.cbegin();
    auto otherIt = other.poly.cbegin();
    auto myEnd = poly.cend();
    auto otherEnd = other.poly.cend();
    TermCmp cmp;
    while(true) {
        if (myIt == myEnd) {
            for (auto it = otherIt; it != otherEnd; ++it) {
                merged.emplace_back(it->var, it->coeff * coeff);
                added.push_back(it->var);
            }
            break;
        }
        if (otherIt == otherEnd) {
            merged.insert(merged.end(), myIt, myEnd);
            break;
        }
        if(cmp(*myIt, *otherIt)) {
            merged.push_back(*myIt);
            ++myIt;
        }
        else if (cmp(*otherIt, *myIt)) {
            merged.emplace_back(otherIt->var, otherIt->coeff * coeff);
            added.push_back(otherIt->var);
            ++otherIt;
        }
        else {
            assert(myIt->var == otherIt->var);
            auto mergedCoeff = myIt->coeff + (otherIt->coeff * coeff);
            if (mergedCoeff.isZero()) {
                removed.push_back(myIt->var);
            }
            else {
                merged.emplace_back(myIt->var, std::move(mergedCoeff));
            }
            ++myIt;
            ++otherIt;
        }
    }
    poly.swap(merged);
    poly.shrink_to_fit();
    return res;
}

void Polynomial::print() const {
    for (auto & term : poly) {
        std::cout << term.coeff << " * " << term.var.x << "v + ";
    }
    std::cout << std::endl;
}