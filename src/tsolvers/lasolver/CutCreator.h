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

class Row {
    std::vector<FastRational> elements;
public:
    explicit Row(ColumnCount cols) {
        elements.resize(cols);
    }

    FastRational &       operator[](std::size_t index)       { return elements[index]; }
    FastRational const & operator[](std::size_t index) const { return elements[index]; }

    std::size_t size() const { return elements.size(); }

    void negate();
    void add(Row const & other, FastRational const & multiple);
};

class RowMatrix {
    std::vector<Row> rows;
public:
    explicit RowMatrix(RowCount rowCount, ColumnCount colCount) {
        rows.reserve(rowCount);
        for (std::size_t i = 0; i < rowCount; ++i) {
            rows.emplace_back(colCount);
        }
    }

    Row &       operator[](std::size_t index)       { return rows[index]; }
    Row const & operator[](std::size_t index) const { return rows[index]; }
};

class Column {
    std::vector<FastRational> elements;
public:
    explicit Column(RowCount rows) {
        elements.resize(rows);
    }

    FastRational &       operator[](std::size_t index)       { return elements[index]; }
    FastRational const & operator[](std::size_t index) const { return elements[index]; }

    std::size_t size() const { return elements.size(); }

    void negate();
    void add(Column const & other, FastRational const & multiple);
};

class ColMatrix {
    std::vector<Column> columns;
public:
    explicit ColMatrix(ColumnCount cols, RowCount rows) {
        columns.reserve(cols);
        for (std::size_t i = 0; i < cols; ++i) {
            columns.emplace_back(rows);
        }
    }

    Column &       operator[](std::size_t index)       { return columns[index]; }
    Column const & operator[](std::size_t index) const { return columns[index]; }

    std::size_t colCount() const { return columns.size(); }
    std::size_t rowCount() const { assert(columns.size()); return columns[0].size(); }

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
