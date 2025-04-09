/*
 *  Copyright (c) 2018-2022, Martin Blicha <martin.blicha@gmail.com>
 *  Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 */

#ifndef OPENSMT_POLYNOMIAL_H
#define OPENSMT_POLYNOMIAL_H

#include <common/numbers/Real.h>

#include <vector>
#include <unordered_map>
#include <functional>
#include <iostream>
#include <algorithm>
#include <cassert>

namespace opensmt {

template<typename VarType>
class PolynomialT {
private:
    struct Term {
        VarType var;
        Real coeff;

        Term(VarType var, Real&& coeff): var{var.x}, coeff{std::move(coeff)} {}
    };
    struct TermCmp {
        bool operator()(const Term& first, const Term& second) { return first.var.x < second.var.x; }
    };
public:
    using poly_t = std::vector<Term>; // Terms are ordered by variable num
private:
    poly_t poly;
    using mergeFunctionInformerType = void(*)(VarType);
public:
    void addTerm(VarType var, Real coeff);
    std::size_t size() const;
    const Real & getCoeff(VarType var) const;
    Real removeVar(VarType var);
    void negate();
    void divideBy(const Real& r);

    template <typename ADD = mergeFunctionInformerType, typename REM = mergeFunctionInformerType>
    void merge(
        PolynomialT const & other,
        Real const & coeff,
        poly_t & tmp_storage,
        ADD informAdded = [](VarType){},
        REM informRemoved = [](VarType){}
    );

    /* Simple version of merge that does not use the hooks and does not need external temporary storage */
    void merge(PolynomialT const & other, Real const & coeff) {
        poly_t tmp_storage;
        return merge(other, coeff, tmp_storage);
    }

    using iterator = typename poly_t::iterator;
    using const_iterator = typename poly_t::const_iterator;

    iterator begin(){
        return poly.begin();
    }
    iterator end() {
        return poly.end();
    }

    const_iterator begin() const {
        return poly.cbegin();
    }
    const_iterator end() const{
        return poly.cend();
    }

    // debug
    bool contains(VarType var) const {
        return findTermForVar(var) != poly.end();
    }

    const_iterator findTermForVar(VarType var) const {
        return std::find_if(poly.begin(), poly.end(), [var](const Term& term) { return term.var == var; });
    }

    iterator findTermForVar(VarType var) {
        return std::find_if(poly.begin(), poly.end(), [var](const Term& term) { return term.var == var; });
    }

    void print() const;
};

template<typename VarType>
template<typename ADD, typename REM>
void PolynomialT<VarType>::merge(PolynomialT<VarType> const & other, Real const & coeff, poly_t & tmp_storage, ADD informAdded,
                  REM informRemoved) {
    if (tmp_storage.size() < this->poly.size() + other.poly.size()) {
        tmp_storage.resize(this->poly.size() + other.poly.size(), Term(VarType::Undef, 0));
    }
    std::size_t storageIndex = 0;
    auto myIt = poly.begin();
    auto otherIt = other.poly.cbegin();
    auto myEnd = poly.end();
    auto otherEnd = other.poly.cend();
    TermCmp cmp;
    Real tmp;
    while(true) {
        if (myIt == myEnd) {
            for (auto it = otherIt; it != otherEnd; ++it) {
                tmp_storage[storageIndex].var = it->var;
                multiplication(tmp_storage[storageIndex].coeff, it->coeff, coeff);
                ++storageIndex;
                informAdded(it->var);
            }
            break;
        }
        if (otherIt == otherEnd) {
            std::move(myIt, myEnd, tmp_storage.begin() + storageIndex);
            storageIndex += myEnd - myIt;
            break;
        }
        if (cmp(*myIt, *otherIt)) {
            tmp_storage[storageIndex] = std::move(*myIt);
            ++storageIndex;
            ++myIt;
        }
        else if (cmp(*otherIt, *myIt)) {
            tmp_storage[storageIndex].var = otherIt->var;
            multiplication(tmp_storage[storageIndex].coeff, otherIt->coeff, coeff);
            ++storageIndex;
            informAdded(otherIt->var);
            ++otherIt;
        }
        else {
            assert(myIt->var == otherIt->var);
            multiplication(tmp, otherIt->coeff, coeff);
            myIt->coeff += tmp;
            if (myIt->coeff.isZero()) {
                informRemoved(myIt->var);
            }
            else {
                tmp_storage[storageIndex] = std::move(*myIt);
                ++storageIndex;
            }
            ++myIt;
            ++otherIt;
        }
    }
    // At this point the right elements are in `tmp_storage`, from beginning to the `storageIndex`.
    // We need to get these elements to `this->poly`. Note that we never change the `tmp_storage` container, we just move out
    // the appropriate elements.
    // However, we observed that we need to shrink `poly` if its size is much smaller than the capacity.
    // The reason is that keeping large free capacity around for many rows blows up the memory
    // (worse case quadratic in the size of the tableau).
    auto polySize = poly.size();
    if (storageIndex > polySize) {
        // In this case we have more elements to move than the current size of the `poly` container.
        // We move the elements that fit the current `poly` size and then we insert the rest of the elements.
        std::move(tmp_storage.begin(), tmp_storage.begin() + polySize, poly.begin());
        poly.insert(poly.end(), std::make_move_iterator(tmp_storage.begin() + polySize), std::make_move_iterator(tmp_storage.begin() + storageIndex));
    }
    else if (/*storageIndex <= poly.size() and */ polySize <= 2 * storageIndex) {
        // In this case we have less elements that need to move than what we currently already have in `poly`, but not too litle.
        // We just move the appropriate elements and destroy the excess elements of `poly`.
        // Since we are removing too many elements, we avoid shrinking which would require re-allocation.
        std::move(tmp_storage.begin(), tmp_storage.begin() + storageIndex, poly.begin());
        poly.erase(poly.begin() + storageIndex, poly.end());
    } else { // poly.size() > 2 * storageIndex
        // This case is similar to case 2, but we have much less elements in the result than currently in `poly`.
        // To avoid too large free capacity in `poly`, we shrink its capacity to exactly the number of elements.
        // It is basically `poly.shrink_to_fit()`, except that `shrink_to_fit` is non-binding.
        std::vector<Term>(std::make_move_iterator(tmp_storage.begin()), std::make_move_iterator(tmp_storage.begin() + storageIndex)).swap(poly);
    }
}

template<typename VarType>
void PolynomialT<VarType>::addTerm(VarType var, Real coeff) {
    assert(!contains(var));
    Term term {var, std::move(coeff)};
    auto it = std::upper_bound(poly.begin(), poly.end(), term, TermCmp{});
    poly.insert(it, std::move(term));
}

template<typename VarType>
unsigned long PolynomialT<VarType>::size() const {
    return poly.size();
}

template<typename VarType>
Real const & PolynomialT<VarType>::getCoeff(VarType var) const {
    assert(contains(var));
    return findTermForVar(var)->coeff;
}

template<typename VarType>
Real PolynomialT<VarType>::removeVar(VarType var) {
    assert(contains(var));
    iterator it = findTermForVar(var);
    auto coeff = std::move(it->coeff);
    poly.erase(it);
    return coeff;
}

template<typename VarType>
void PolynomialT<VarType>::negate() {
    for(auto & term : poly) {
        term.coeff.negate();
    }
}

template<typename VarType>
void PolynomialT<VarType>::divideBy(const Real &r) {
    for(auto & term : poly) {
        term.coeff /= r;
    }
}
template<typename VarType>
void PolynomialT<VarType>::print() const {
    for (auto & term : poly) {
        std::cout << term.coeff << " * " << term.var.x << "v + ";
    }
    std::cout << std::endl;
}

}

#endif //OPENSMT_POLYNOMIAL_H
