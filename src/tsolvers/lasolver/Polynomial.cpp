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

void
Polynomial::merge(const Polynomial &other, const opensmt::Real &coeff, std::function<void(LVRef)> informAdded,
                  std::function<void(LVRef)> informRemoved) {
    decltype(poly) merged;
    merged.reserve(this->poly.size() + other.poly.size());
    auto myIt = std::make_move_iterator(poly.begin());
    auto otherIt = other.poly.cbegin();
    auto myEnd = std::make_move_iterator(poly.end());
    auto otherEnd = other.poly.cend();
    TermCmp cmp;
    while(true) {
        if (myIt == myEnd) {
            for (auto it = otherIt; it != otherEnd; ++it) {
                merged.emplace_back(it->var, it->coeff * coeff);
                informAdded(it->var);
            }
            break;
        }
        if (otherIt == otherEnd) {
            merged.insert(merged.end(), myIt, myEnd);
            break;
        }
        if (cmp(*myIt, *otherIt)) {
            merged.emplace_back(*myIt);
            ++myIt;
        }
        else if (cmp(*otherIt, *myIt)) {
            merged.emplace_back(otherIt->var, otherIt->coeff * coeff);
            informAdded(otherIt->var);
            ++otherIt;
        }
        else {
            assert(myIt->var == otherIt->var);
            auto mergedCoeff = otherIt->coeff * coeff;
            mergedCoeff += myIt->coeff;
            if (mergedCoeff.isZero()) {
                informRemoved(myIt->var);
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
}

void
Polynomial::merge(const Polynomial &other, const opensmt::Real &coeff, std::function<void(LVRef)> informAdded,
                  std::function<void(LVRef)> informRemoved, std::vector<Term>& storage) {
    storage.reserve(this->poly.size() + other.poly.size());
    auto myIt = std::make_move_iterator(poly.begin());
    auto otherIt = other.poly.cbegin();
    auto myEnd = std::make_move_iterator(poly.end());
    auto otherEnd = other.poly.cend();
    TermCmp cmp;
    while(true) {
        if (myIt == myEnd) {
            for (auto it = otherIt; it != otherEnd; ++it) {
                storage.emplace_back(it->var, it->coeff * coeff);
                informAdded(it->var);
            }
            break;
        }
        if (otherIt == otherEnd) {
            storage.insert(storage.end(), myIt, myEnd);
            break;
        }
        if (cmp(*myIt, *otherIt)) {
            storage.emplace_back(*myIt);
            ++myIt;
        }
        else if (cmp(*otherIt, *myIt)) {
            storage.emplace_back(otherIt->var, otherIt->coeff * coeff);
            informAdded(otherIt->var);
            ++otherIt;
        }
        else {
            assert(myIt->var == otherIt->var);
            auto mergedCoeff = otherIt->coeff * coeff;
            mergedCoeff += myIt->coeff;
            if (mergedCoeff.isZero()) {
                informRemoved(myIt->var);
            }
            else {
                storage.emplace_back(myIt->var, std::move(mergedCoeff));
            }
            ++myIt;
            ++otherIt;
        }
    }
    std::vector<Term>(std::make_move_iterator(storage.begin()), std::make_move_iterator(storage.end())).swap(poly);
    storage.clear();
}



void Polynomial::print() const {
    for (auto & term : poly) {
        std::cout << term.coeff << " * " << term.var.x << "v + ";
    }
    std::cout << std::endl;
}