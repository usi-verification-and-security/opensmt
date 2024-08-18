/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *                      Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_SPARSEMATRIX_H
#define OPENSMT_SPARSEMATRIX_H

#include "Polynomial.h"

#include <common/inttypes.h>

#include <cassert>
#include <numeric>
#include <vector>

namespace opensmt {
struct ColumnCount {
    uint32_t count;
    operator uint32_t() const { return count; }
};

struct RowCount {
    uint32_t count;
    operator uint32_t() const { return count; }
};

using ColIndex = ColumnCount;
using RowIndex = RowCount;

struct IndexType {
    uint32_t x;
    bool operator==(IndexType const o) const { return x == o.x; }
    static IndexType const Undef;
};

inline constexpr IndexType IndexType::Undef = IndexType{INT32_MAX};

class SparseColMatrix {
public:
    using ColumnPolynomial = PolynomialT<IndexType>;
    using TermVec = std::vector<std::pair<IndexType, Real>>;

    class Col {
    public:
        Col() = default;
        Col(Col const &) = delete;
        Col & operator=(Col const &) = delete;
        Col(Col &&) = default;
        Col & operator=(Col &&) = default;
        void setPolynomial(ColumnPolynomial && _poly) {
            assert(this->poly.size() == 0);
            this->poly = std::move(_poly);
        }

        uint32_t size() const { return poly.size(); }

        void negate();
        void add(Col const & other, Real const & multiple);

        bool isFirst(RowIndex row) const { return poly.size() > 0 and poly.begin()->var.x == row.count; }
        Real const * tryGetFirstCoeff() const { return poly.size() > 0 ? &poly.begin()->coeff : nullptr; }
        Real const & getFirstCoeff() const {
            assert(poly.size() > 0);
            return poly.begin()->coeff;
        }
        Real const * tryGetCoeffFor(RowIndex rowIndex) const;

        Real product(std::vector<Real> const & values) const;
        TermVec toVector() const;

    private:
        ColumnPolynomial poly;
    };

    explicit SparseColMatrix(RowCount rowCount, ColumnCount colCount) : _rowCount(rowCount), _colCount{colCount} {
        cols.resize(colCount.count);
        colPermutation.resize(colCount);
        std::iota(colPermutation.begin(), colPermutation.end(), 0);
    }

    SparseColMatrix(SparseColMatrix const &) = delete;
    SparseColMatrix & operator=(SparseColMatrix const &) = delete;
    SparseColMatrix(SparseColMatrix &&) = default;
    SparseColMatrix & operator=(SparseColMatrix &&) = default;

    Col & operator[](uint32_t index) { return cols[colPermutation[index]]; }
    Col const & operator[](uint32_t index) const { return cols[colPermutation[index]]; }

    void swapCols(uint32_t first, uint32_t second) { std::swap(colPermutation[first], colPermutation[second]); }

    uint32_t colCount() const { return _colCount; }
    uint32_t rowCount() const { return _rowCount; }

    void setColumn(ColIndex colIndex, ColumnPolynomial && poly) {
        assert(colIndex < _colCount);
        cols[colIndex].setPolynomial(std::move(poly));
    }

private:
    RowCount _rowCount;
    ColumnCount _colCount;
    std::vector<Col> cols;
    std::vector<uint32_t> colPermutation;
};

class HermiteNormalForm {
public:
    struct HNFOperationsResult {
        SparseColMatrix operations;
        uint32_t HNFdimension;
    };

    HNFOperationsResult operator()(SparseColMatrix &&) const;
};

struct SparseLinearSystem {
    SparseColMatrix A;
    std::vector<Real> rhs;
};
} // namespace opensmt

#endif // OPENSMT_SPARSEMATRIX_H
