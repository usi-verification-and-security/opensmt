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

struct ColumnCount {
    std::size_t count;
    operator std::size_t() const { return count; }
};

using ColIndex = ColumnCount;

struct RowCount {
    std::size_t count;
    operator std::size_t() const { return count; }
};

using RowIndex = RowCount;

class RowMatrix {
    RowCount rows;
    ColumnCount cols;
    std::vector<FastRational> elements;
    std::vector<std::size_t> rowPermutation;
public:
    class RowView {
        RowMatrix * matrix;
        RowIndex rowIndex;
        ColumnCount colCount;
    public:
        explicit RowView(RowMatrix & matrix, RowIndex rowIndex, ColumnCount colCount) :
                matrix(&matrix), rowIndex(rowIndex), colCount(colCount) {}

        FastRational &       operator[](std::size_t index)       { return matrix->elements[rowIndex * colCount + index]; }
        FastRational const & operator[](std::size_t index) const { return matrix->elements[rowIndex * colCount + index]; }

        std::size_t size() const { return colCount; }

        opensmt::span<FastRational> toSpan();
        opensmt::span<const FastRational> toSpan() const;

        void negate();
        void add(RowView const & other, FastRational const & multiple);
    };


    explicit RowMatrix(RowCount rowCount, ColumnCount colCount) : rows(rowCount), cols{colCount} {
        elements.resize(rowCount * colCount, 0);
        rowPermutation.resize(rowCount);
        std::iota(rowPermutation.begin(), rowPermutation.end(), 0);
    }

    RowMatrix(RowMatrix const &) = delete;
    RowMatrix(RowMatrix &&) = default;

    RowView       operator[](std::size_t index)       { return RowView(*this, RowIndex{rowPermutation[index]}, cols); }
//    RowView const operator[](std::size_t index) const { return RowView(*this, RowIndex{index}, cols); }

    void swapRows(std::size_t first, std::size_t second) { std::swap(rowPermutation[first], rowPermutation[second]); }

    std::size_t colCount() const { return cols; }
    std::size_t rowCount() const { return rows; }
};


class ColMatrix {
    RowCount rows;
    ColumnCount cols;
    std::vector<FastRational> elements;
    std::vector<std::size_t> colPermutation;
public:
    class ColView {
        ColMatrix * matrix;
        ColIndex colIndex;
        RowCount rowCount;
    public:
        explicit ColView(ColMatrix & matrix, ColIndex colIndex, RowCount rowCount) :
        matrix(&matrix), colIndex(colIndex), rowCount(rowCount) {}

        FastRational &       operator[](std::size_t index)       { return matrix->elements[colIndex * rowCount + index]; }
        FastRational const & operator[](std::size_t index) const { return matrix->elements[colIndex * rowCount + index]; }

        std::size_t size() const { return rowCount; }

        opensmt::span<FastRational> toSpan();
        opensmt::span<const FastRational> toSpan() const;

        void negate();
        void add(ColView const & other, FastRational const & multiple);
    };

    explicit ColMatrix(ColumnCount colCount, RowCount rowCount) : rows(rowCount), cols(colCount) {
        elements.resize(rowCount * colCount, 0);
        colPermutation.resize(rowCount);
        std::iota(colPermutation.begin(), colPermutation.end(), 0);
    }

    ColMatrix(ColMatrix const &) = delete;
    ColMatrix(ColMatrix &&) = default;

    ColView       operator[](std::size_t index)       { return ColView(*this, ColIndex{colPermutation[index]}, rows); }
//    ColView const operator[](std::size_t index) const { return ColView(*this, ColIndex{index}, rows); }

    void swapCols(std::size_t first, std::size_t second) { std::swap(colPermutation[first], colPermutation[second]); }

    std::size_t colCount() const { return cols; }
    std::size_t rowCount() const { return rows; }

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

    PTRef cut(std::vector<DefiningConstaint> constraints);
};


#endif //OPENSMT_CUTCREATOR_H
