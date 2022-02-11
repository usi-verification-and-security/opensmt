/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *                      Antti Hyvarinen <antti.hyvarinen@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_SPARSEMATRIX_H
#define OPENSMT_SPARSEMATRIX_H

#include "osmtinttypes.h"
#include "Polynomial.h"
#include <vector>
#include <numeric>

struct ColumnCount {
    uint32_t count;
    operator uint32_t () const { return count; }
};

using ColIndex = ColumnCount;

struct RowCount {
    uint32_t count;
    operator uint32_t () const { return count; }
};

using RowIndex = RowCount;



class SparseColMatrix {
public:
    using TermVec = std::vector<std::pair<LVRef, FastRational>>;
    class Col {
        Polynomial poly;
    public:
        Col() = default;
        Col(Col const &) = delete;
        Col(Col &&) = default;
        void setPolynomial(Polynomial && _poly)  {
            assert(this->poly.size() == 0);
            this->poly = std::move(_poly);
        }

        uint32_t size() const { return poly.size(); }

        void negate();
        void add(Col const & other, FastRational const & multiple);

        bool isFirst(RowIndex row) const { return poly.size() > 0 and poly.begin()->var.x == row.count; }
        FastRational const * tryGetFirstCoeff() const { return poly.size() > 0 ? &poly.begin()->coeff : nullptr; }
        FastRational const & getFirstCoeff() const { assert(poly.size() > 0); return poly.begin()->coeff; }
        FastRational const * tryGetCoeffFor(RowIndex rowIndex) const;

        FastRational product(std::vector<FastRational> const & values) const;
        TermVec toVector() const;
    };

private:
    RowCount _rowCount;
    ColumnCount _colCount;
    std::vector<Col> cols;
    std::vector<uint32_t> colPermutation;

public:
    explicit SparseColMatrix(RowCount rowCount, ColumnCount colCount) : _rowCount(rowCount), _colCount{colCount} {
        cols.resize(colCount.count);
        colPermutation.resize(colCount);
        std::iota(colPermutation.begin(), colPermutation.end(), 0);
    }

    SparseColMatrix(SparseColMatrix const &) = delete;
    SparseColMatrix(SparseColMatrix &&) = default;

    Col &       operator[](uint32_t index)       { return cols[colPermutation[index]]; }
    Col const & operator[](uint32_t index) const { return cols[colPermutation[index]]; }

    void swapCols(uint32_t first, uint32_t second) { std::swap(colPermutation[first], colPermutation[second]); }

    uint32_t colCount() const { return _colCount; }
    uint32_t rowCount() const { return _rowCount; }

    void setColumn(ColIndex colIndex, Polynomial && poly) {
        assert(colIndex < _colCount);
        cols[colIndex].setPolynomial(std::move(poly));
    }
};

class HermiteNormalForm {
public:
    struct HNFOperationsResult {
        SparseColMatrix operations;
        uint32_t HNFdimension;
    };
    HNFOperationsResult operator() (SparseColMatrix &&) const;
};

struct SparseLinearSystem {
    SparseColMatrix A;
    std::vector<FastRational> rhs;
};

#endif //OPENSMT_SPARSEMATRIX_H
