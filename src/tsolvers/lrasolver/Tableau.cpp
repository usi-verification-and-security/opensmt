//
// Created by Martin Blicha on 31.03.18.
//

#include "Tableau.h"
#include <iostream>

using namespace opensmt;
namespace {
    template<class C, class E>
    inline bool contains(const C & container, const E & elem){
        return container.find(elem) != container.end();
    }

    inline bool isOne(const opensmt::Real & r){
        return r == 1;
    }
}

void Tableau::nonbasicVar(LVRef v) {
    if(contains(nonbasic_vars, v)) {return;}
    assert(!contains(basic_vars, v));
    newNonbasicVar(v);
}

void Tableau::newNonbasicVar(LVRef v) {
    assert(!contains(nonbasic_vars, v));
    while(cols.size() <= v.x) {
        cols.emplace_back();
    }
    while(rows.size() <= v.x) {
        rows.emplace_back();
    }
    assert(!cols[v.x]);
    cols[v.x] = std::unique_ptr<Column>(new Column());
    nonbasic_vars.insert(v);
}

void Tableau::newBasicVar(LVRef v, std::unique_ptr<Polynomial> poly) {
    assert(!contains(basic_vars, v));
    while(cols.size() <= v.x) {
        cols.emplace_back();
    }
    while(rows.size() <= v.x) {
        rows.emplace_back();
    }
    for(auto const & term : *poly) {
        assert(cols[term.var.x]);
        addRowToColumn(v, term.var);
    }
    addRow(v, std::move(poly));
    basic_vars.insert(v);

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

const Polynomial & Tableau::getRowPoly(LVRef basicVar) const {
    assert(rows[basicVar.x]);
    return *rows[basicVar.x];
}

Polynomial & Tableau::getRowPoly(LVRef basicVar) {
    assert(rows[basicVar.x]);
    return *rows[basicVar.x];
}

const Tableau::rows_t & Tableau::getRows() const {
    return rows;
}

const Tableau::vars_t & Tableau::getNonBasicVars() const {
    return nonbasic_vars;
}

void Tableau::addRow(LVRef v, std::unique_ptr<Polynomial> p) {
    assert(!rows[v.x]);
    rows[v.x] = std::move(p);
}

std::unique_ptr<Polynomial> Tableau::removeRow(LVRef v) {
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
    return contains(basic_vars, v) || contains(nonbasic_vars, v);
}

void Tableau::pivot(LVRef bv, LVRef nv) {
    assert(isBasic(bv));
    assert(isNonBasic(nv));
    basic_vars.erase(bv);
    basic_vars.insert(nv);
    nonbasic_vars.erase(nv);
    nonbasic_vars.insert(bv);
    assert(cols[nv.x]);
    assert(!cols[bv.x]);
    // compute the polynomial for nv
    assert(rows[bv.x]);
    assert(!rows[nv.x]);
    {
        Polynomial & nvPoly = getRowPoly(bv);
        const auto coeff = nvPoly.removeVar(nv);
        Real bvCoeff{1};
        if (!isOne(coeff)) {
            nvPoly.divideBy(coeff);
            bvCoeff /= coeff;
        }
        nvPoly.negate();
        nvPoly.addTerm(bv, bvCoeff);
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
        if(rowVar == nv || !isActive(rowVar)) {
            continue;
        }
        // update the polynomials
        auto & poly = getRowPoly(rowVar);
        const auto nvCoeff = poly.removeVar(nv);
        auto changes = poly.merge(nvPoly, nvCoeff);
        // update the column information
        assert(cols[bv.x]);
        assert(std::find(changes.added.begin(), changes.added.end(), bv) != changes.added.end());
        for (const auto & addedVar : changes.added) {
            if (addedVar == bv) { continue; }
            assert(cols[addedVar.x]);
            assert(!contains(getColumn(addedVar), rowVar));
            addRowToColumn(rowVar, addedVar);
        }
        for (const auto & removedVar : changes.removed) {
            assert(cols[removedVar.x]);
            assert(contains(getColumn(removedVar), rowVar));
            removeRowFromColumn(rowVar, removedVar);
        }
    }
    assert(!cols[nv.x]);
    assert(cols[bv.x]);
    assert(!rows[bv.x]);
    assert(rows[nv.x]);
}

void Tableau::clear() {
    this->rows.clear();
    this->cols.clear();
    this->basic_vars.clear();
    this->nonbasic_vars.clear();
}

bool Tableau::isActive(LVRef basicVar) const { return true;}

bool Tableau::isBasic(LVRef v) const {return contains(basic_vars, v);}
bool Tableau::isNonBasic(LVRef v) const {return contains(nonbasic_vars, v);}

void Tableau::print() const {
    std::cout << "Basic vars: ";
    for (auto var : basic_vars) {
        std::cout << var.x << " ";
    }
    std::cout << '\n';

    std::cout << "Non-basic vars: ";
    for (auto var : nonbasic_vars) {
        std::cout << var.x << " ";
    }
    std::cout << '\n';

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
    for (auto nv : nonbasic_vars)  {
        res &= (cols[nv.x] != nullptr);
        assert(res);
    }
    for(unsigned i = 0; i < cols.size(); ++i) {
        LVRef var {i};
        if(!cols[i]){
            // there could be empty non-basic variables; e.g. from atoms x <= 5
            // or here, we could have columns also or basic variables, which should be empty
            continue;
        }
        res &= contains(nonbasic_vars, var);
        assert(res);
        for(auto row : *cols[i]) {
            res &= this->getRowPoly(row).contains(var);
            assert(res);
        }
    }

    for(unsigned i = 0; i < rows.size(); ++i) {
        LVRef var {i};
        if(!isActive(var)) {
            continue;
        }
        if (!rows[i]) { continue; }
        res &= contains(basic_vars, var);
        assert(res);
        for (auto const & term : *rows[i]) {
            auto termVar = term.var;
            res &= contains(nonbasic_vars, termVar) && cols[termVar.x];
            assert(res);
            res &= contains(getColumn(termVar), var);
            assert(res);
        }
    }
    return res;
}

std::vector<std::pair<LVRef, Polynomial>>
Tableau::doGaussianElimination(std::function<bool(LVRef)> shouldEliminate) {
//    print();
    assert(checkConsistency());
    std::vector<std::pair<LVRef, Polynomial>> removed;
    auto old_nonbasic_vars = nonbasic_vars;
    for (auto var : old_nonbasic_vars) {
        assert(cols[var.x]);
        if (!shouldEliminate(var) || cols[var.x]->empty()) { continue; }
        // we are going to eliminate this column variable from the tableau
        // pick row which we are going to use to express this variable
        auto const & col = getColumn(var);
        // finds the row with the minimal size of the polynomial
        LVRef chosen_row = *(col.begin());
        auto min_size = rows[chosen_row.x]->size();
        for (auto it = ++col.begin(); it != col.end(); ++it) {
            auto size = rows[it->x]->size();
            if (size < min_size) {
                min_size = size;
                chosen_row = *it;
            }
        }
        // remember the original polynomial
        // remove the row completly, update the column information; TODO: this can be done together in one method
        auto poly_ptr = removeRow(chosen_row);
        auto & poly = *poly_ptr;
        for (auto const & term : poly) {
            auto l_var = term.var;
            assert(cols[l_var.x]);
            removeRowFromColumn(chosen_row, l_var);
        }
        assert(contains(basic_vars, chosen_row));
        basic_vars.erase(chosen_row);
        nonbasic_vars.insert(chosen_row);
        // make sure the row variable has a ready column representation
        assert(!cols[chosen_row.x]);
        cols[chosen_row.x] = std::unique_ptr<Column>(new Column());
        // now express the chosen_row in terms of column variable
        {
            auto coeff = poly.removeVar(var);
            coeff.negate();
            poly.addTerm(chosen_row, -1);
            poly.divideBy(coeff);
        }
        // remember the polynomial for removed var
        removed.emplace_back(var, poly);
        // now substitute in other rows where var is present
        for (auto rowVar : col) {
            if (rowVar == chosen_row) { continue; }
            assert(rows[rowVar.x]);
            auto & row_poly = getRowPoly(rowVar);
            auto coeff = row_poly.removeVar(var);
            auto res = row_poly.merge(poly, coeff);
            // process added and removed vars
            for (const auto & addedVar : res.added) {
                assert(cols[addedVar.x]);
                assert(!contains(*cols[addedVar.x], rowVar));
                addRowToColumn(rowVar, addedVar);
            }
            for (const auto & removedVar : res.removed) {
                assert(cols[removedVar.x]);
                assert(cols[removedVar.x]);
                removeRowFromColumn(rowVar, removedVar);
            }
        }
        // remove the eliminated column
        assert(contains(nonbasic_vars, var));
        nonbasic_vars.erase(var);
        assert(cols[var.x]);
        // Destroy the column object
        cols[var.x].reset();
        assert(!cols[var.x]);
//        print();
    }
    assert(checkConsistency());
    return removed;
}