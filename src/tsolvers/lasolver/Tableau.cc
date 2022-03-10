//
// Created by Martin Blicha on 31.03.18.
//

#include "Tableau.h"
#include <iostream>

#ifdef SIMPLEX_DEBUG
#define simplex_assert(x) assert(x)
#else
#define simplex_assert(x)
#endif // SIMPLEX_DEBUG

using namespace opensmt;
namespace {
    template<class C, class E>
    inline bool contains(const C & container, const E & elem){
        return container.find(elem) != container.end();
    }
}

void Tableau::nonbasicVar(LVRef v) {
    if (isProcessed(v)) { return; }
    newNonbasicVar(v);
}

void Tableau::newNonbasicVar(LVRef v) {
    assert(!isProcessed(v));
    ensureTableauReadyFor(v);
    assert(!cols[v.x]);
    cols[v.x] = std::make_unique<Column>();
    varTypes[getVarId(v)] = VarType::NONBASIC;
}

void Tableau::newRow(LVRef v, std::unique_ptr<Polynomial> poly) {
    assert(!isProcessed(v));
    ensureTableauReadyFor(v);
    addRow(v, std::move(poly));
    varTypes[getVarId(v)] = VarType::QUASIBASIC;
    normalizeRow(v);

}

std::size_t Tableau::getNumOfCols() const {
    return cols.size();
}

std::size_t Tableau::getPolySize(LVRef basicVar) const {
    assert(rows[basicVar.x]);
    return rows[basicVar.x]->size();
}

const opensmt::Real & Tableau::getCoeff(LVRef basicVar, LVRef nonBasicVar) const {
    assert(rows[basicVar.x]);
    return rows[basicVar.x]->getCoeff(nonBasicVar);
}

const Tableau::column_t & Tableau::getColumn(LVRef nonBasicVar) const {
    assert(cols[nonBasicVar.x]);
    return *cols[nonBasicVar.x];
}

const Tableau::Polynomial & Tableau::getRowPoly(LVRef basicVar) const {
    assert(rows[basicVar.x]);
    return *rows[basicVar.x];
}

Tableau::Polynomial & Tableau::getRowPoly(LVRef basicVar) {
    assert(rows[basicVar.x]);
    return *rows[basicVar.x];
}

const Tableau::rows_t & Tableau::getRows() const {
    return rows;
}

std::vector<LVRef> Tableau::getNonBasicVars() const {
    std::vector<LVRef> res;
    res.resize(varTypes.size());
    for (unsigned i = 0; i < varTypes.size(); ++i) {
        if (varTypes[i] == VarType::NONBASIC) {
            res.push_back(LVRef{i});
        }
    }
    return res;
}

void Tableau::addRow(LVRef v, std::unique_ptr<Polynomial> p) {
    assert(!rows[v.x]);
    rows[v.x] = std::move(p);
}

std::unique_ptr<Tableau::Polynomial> Tableau::removeRow(LVRef v) {
    assert(rows[v.x]);
    std::unique_ptr<Polynomial> res;
    assert(!res);
    res.swap(rows[v.x]);
    return res;
}

void Tableau::moveRowFromTo(LVRef from, LVRef to) {
    assert(!rows[to.x]);
    assert(rows[from.x]);
    rows[to.x] = std::move(rows[from.x]);
}

void Tableau::moveColFromTo(LVRef from, LVRef to) {
    assert(!cols[to.x]);
    assert(cols[from.x]);
    cols[to.x] = std::move(cols[from.x]);
}

bool Tableau::isProcessed(LVRef v) const {
    return varTypes.size() > getVarId(v) && varTypes[getVarId(v)] != VarType::NONE;
}

void Tableau::pivot(LVRef bv, LVRef nv) {
    assert(isBasic(bv));
    assert(isNonBasic(nv));
    varTypes[getVarId(bv)] = VarType::NONBASIC;
    varTypes[getVarId(nv)] = VarType::BASIC;
    assert(cols[nv.x]);
    assert(!cols[bv.x]);
    // compute the polynomial for nv
    assert(rows[bv.x]);
    assert(!rows[nv.x]);
    {
        Polynomial & nvPoly = getRowPoly(bv);
        const auto coeff = nvPoly.removeVar(nv);
        if (not coeff.isOne()) {
            nvPoly.divideBy(coeff);
        }
        nvPoly.negate();
        nvPoly.addTerm(bv, coeff.inverse());
    }

    // remove row for bv, add row for nv
    moveRowFromTo(bv, nv);
    // move the column from nv tto bv
    moveColFromTo(nv, bv);

    Polynomial & nvPoly = getRowPoly(nv);
    // update column information regarding this one poly
    for(auto & term : nvPoly) {
        auto var = term.var;
        assert(cols[var.x]);
        removeRowFromColumn(bv, var);
        addRowToColumn(nv, var);
    }

    // for all (active) rows containing nv, substitute
    for (auto rowVar : getColumn(bv)) {
        if(rowVar == nv || isQuasiBasic(rowVar)) {
            continue;
        }
        // update the polynomials
        auto & poly = getRowPoly(rowVar);
        const auto nvCoeff = poly.removeVar(nv);
        poly.merge(nvPoly, nvCoeff, tmp_storage,
                // informAdded
                   [this, bv, rowVar](LVRef addedVar) {
                       if (addedVar == bv) { return; }
                       assert(cols[addedVar.x]);
                       assert(!contains(getColumn(addedVar), rowVar));
                       addRowToColumn(rowVar, addedVar);
                   },
                // informRemoved
                   [this, rowVar](LVRef removedVar) {
                       assert(cols[removedVar.x]);
                       assert(contains(getColumn(removedVar), rowVar));
                       removeRowFromColumn(rowVar, removedVar);
                   }
        );
    }
    assert(!cols[nv.x]);
    assert(cols[bv.x]);
    assert(!rows[bv.x]);
    assert(rows[nv.x]);
}

void Tableau::clear() {
    this->rows.clear();
    this->cols.clear();
    this->varTypes.clear();
}

bool Tableau::isBasic(LVRef v) const
    {return varTypes.size() > getVarId(v) && varTypes[getVarId(v)] == VarType::BASIC;}
bool Tableau::isNonBasic(LVRef v) const
    {return varTypes.size() > getVarId(v) && varTypes[getVarId(v)] == VarType::NONBASIC;}
bool Tableau::isQuasiBasic(LVRef v) const
    {return varTypes.size() > getVarId(v) && varTypes[getVarId(v)] == VarType::QUASIBASIC;}

void Tableau::print() const {
    std::cout << "Rows:\n";
    for(unsigned i = 0; i != rows.size(); ++i) {
        if (!rows[i]) { continue; }
        std::cout << "Var of the row: " << i << ';';
        for (const auto & term : this->getRowPoly(LVRef{i})) {
            std::cout << "( " << term.coeff << " | " << term.var.x << " ) ";
        }
        std::cout << '\n';
    }
    std::cout << '\n';
    std::cout << "Columns:\n";
    for(unsigned i = 0; i != cols.size(); ++i) {
        if(!cols[i]) { continue; }
        std::cout << "Var of the column: " << i << "; Contains: ";
        for (auto var : getColumn(LVRef{i})) {
            std::cout << var.x << ' ';
        }
        std::cout << '\n';
    }
    std::cout << '\n';
}

bool Tableau::checkConsistency() const {
    bool res = true;
    for(unsigned i = 0; i < cols.size(); ++i) {
        LVRef var {i};
        if (isNonBasic(var)) {
            res &= (cols[i] != nullptr);
            assert(res);
            for(auto row : *cols[i]) {
                res &= this->getRowPoly(row).contains(var);
                assert(res);
            }
        }
        else{
            assert(!cols[i]);
        }
    }

    for(unsigned i = 0; i < rows.size(); ++i) {
        LVRef var {i};
        if(isQuasiBasic(var)) {
            continue;
        }
        if (!rows[i]) { assert(isNonBasic(var)); continue; }
        res &= isBasic(var);
        assert(res);
        for (auto const & term : *rows[i]) {
            auto termVar = term.var;
            res &= isNonBasic(termVar) && cols[termVar.x];
            assert(res);
            res &= contains(getColumn(termVar), var);
            assert(res);
        }
    }
    return res;
}

// Makes sures the representing polynomial of this row contains only nonbasic variables
void Tableau::normalizeRow(LVRef v) {
    assert(isQuasiBasic(v)); // Do not call this for non quasi rows
    Polynomial & row = getRowPoly(v);
    std::vector<LVRef> toEliminate;
    for (auto const & term : row) {
        if (isQuasiBasic(term.var)) {
            normalizeRow(term.var);
            toEliminate.push_back(term.var);
        }
        if (isBasic(term.var)) {
            toEliminate.push_back(term.var);
        }
    }
    for (LVRef var : toEliminate) {
        auto const coeff = row.removeVar(var);
        row.merge(getRowPoly(var), coeff, tmp_storage);
    }
}

// Eliminates basic variables from representation of this row.
void Tableau::quasiToBasic(LVRef v) {
    assert(isQuasiBasic(v));
    normalizeRow(v);
    for (auto const & term : getRowPoly(v)) {
        addRowToColumn(v, term.var);
    }
    varTypes[getVarId(v)] = VarType::BASIC;
    assert(isBasic(v));
    simplex_assert(checkConsistency());
}

void Tableau::basicToQuasi(LVRef v) {
    assert(isBasic(v));
    varTypes[getVarId(v)] = VarType::QUASIBASIC;
    assert(isQuasiBasic(v));

    Polynomial & row = getRowPoly(v);
    for (auto & term : row) {
        assert(isNonBasic(term.var));
        removeRowFromColumn(v, term.var);
    }
    simplex_assert(checkConsistency());
}

void Tableau::ensureTableauReadyFor(LVRef v) {
    auto id = getVarId(v);
    while(cols.size() <= id) {
        cols.emplace_back();
    }
    while(rows.size() <= id) {
        rows.emplace_back();
    }
    while(varTypes.size() <= id) {
        varTypes.push_back(VarType::NONE);
    }
}
