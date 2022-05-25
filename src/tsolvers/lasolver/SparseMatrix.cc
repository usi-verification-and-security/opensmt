/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#include "SparseMatrix.h"


void SparseColMatrix::Col::negate() {
    this->poly.negate();
}

void SparseColMatrix::Col::add(Col const & other, opensmt::Real const & multiple) {
    this->poly.merge(other.poly, multiple);
}

opensmt::Real SparseColMatrix::Col::product(const std::vector<FastRational> & values) const {
    opensmt::Real sum = 0;
    for (auto const & term : poly) {
        uint32_t index = term.var.x;
        assert(index < values.size());
        sum += term.coeff * values[index];
    }
    return sum;
}

SparseColMatrix::TermVec SparseColMatrix::Col::toVector() const {
    std::vector<std::pair<IndexType, FastRational>> args;
    args.reserve(poly.size());
    for (auto & term : poly) {
        args.emplace_back(term.var, term.coeff);
    }
    return args;
}

const FastRational * SparseColMatrix::Col::tryGetCoeffFor(RowIndex rowIndex) const {
    IndexType bound {rowIndex.count};
    auto it = std::lower_bound(poly.begin(), poly.end(), bound, [](auto const & term, IndexType val) {
        return term.var.x < val.x;
    });
    if (it == poly.end()) { return nullptr; }
    return it->var == bound ? &it->coeff : nullptr;
}