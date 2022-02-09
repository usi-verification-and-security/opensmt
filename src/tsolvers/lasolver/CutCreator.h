/*
 *  Copyright (c) 2022, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef OPENSMT_CUTCREATOR_H
#define OPENSMT_CUTCREATOR_H

#include "ArithLogic.h"
#include "Real.h"
#include "Polynomial.h"

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

class ColMatrix {
public:
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
        PTRef buildCutConstraint(std::vector<PTRef> const & toVarMap, ArithLogic & logic) const;
    };

private:
    RowCount _rowCount;
    ColumnCount _colCount;
    std::vector<Col> cols;
    std::vector<uint32_t> colPermutation;

public:
    explicit ColMatrix(RowCount rowCount, ColumnCount colCount) : _rowCount(rowCount), _colCount{colCount} {
        cols.resize(colCount.count);
        colPermutation.resize(colCount);
        std::iota(colPermutation.begin(), colPermutation.end(), 0);
    }

    ColMatrix(ColMatrix const &) = delete;
    ColMatrix(ColMatrix &&) = default;

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

class CutCreator {
private:
    ArithLogic & logic;
    std::function<FastRational(PTRef)> varValue;

    FastRational evaluate(PTRef var) const { assert(logic.isVar(var)); return varValue(var); }
public:
    CutCreator(ArithLogic & logic, std::function<FastRational(PTRef)> varValue) : logic(logic), varValue(varValue) {}

    struct DefiningConstaint {
        PTRef lhs;
        opensmt::Real rhs;
    };

    PTRef cut(std::vector<DefiningConstaint> const & constraints);
};


#endif //OPENSMT_CUTCREATOR_H
