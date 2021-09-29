/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>
        Aliaksei Tsitovich <aliaksei.tsitovich@gmail.com>

OpenSMT2 -- copyright (C) 2012 - 2015, Antti Hyvarinen
OpenSMT -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#include "LA.h"

void LAExpression::initialize(PTRef e, bool do_canonize) {
    assert(logic.isNumEq(e) || logic.isNumLeq(e));

    vector<PTRef> curr_term;
    vector<opensmt::Real> curr_const;

    PTRef lhs = logic.getPterm(e)[0];
    PTRef rhs = logic.getPterm(e)[1];
    curr_term.push_back(lhs);
    curr_const.push_back(1);
    curr_term.push_back(rhs);
    curr_const.push_back(-1);

    while (!curr_term.empty()) {
        PTRef t = curr_term.back();
        curr_term.pop_back();
        opensmt::Real c = curr_const.back();
        curr_const.pop_back();
        // Only 3 cases are allowed
        //
        // If it is plus, enqueue the arguments with same constant
        if (logic.isNumPlus(t)) {
            const Pterm & term = logic.getPterm(t);
            for (int i = 0; i < term.size(); i++) {
                PTRef arg = term[i];
                curr_term.push_back(arg);
                curr_const.push_back(c);
            }
        } else if (logic.isNumTimes(t)) {
            // If it is times, then one side must be constant, other
            // is enqueued with a new constant
            const Pterm & term = logic.getPterm(t);
            assert(term.size() == 2);
            PTRef x = term[0];
            PTRef y = term[1];
            assert(logic.isConstant(x) || logic.isConstant(y));
            if (logic.isConstant(y)) {
                PTRef tmp = y;
                y = x;
                x = tmp;
            }
            opensmt::Real new_c = logic.getNumConst(x);
            new_c = new_c * c;
            curr_term.push_back(y);
            curr_const.push_back(std::move(new_c));
        } else {
            // Otherwise it is a variable, Ite, UF or constant
            assert(logic.isNumVarLike(t) || logic.isConstant(t) || logic.isUF(t));
            if (logic.isConstant(t)) {
                const opensmt::Real tval = logic.getNumConst(t);
                polynome[PTRef_Undef] += tval * c;
            } else {
                auto it = polynome.find(t);
                if (it != polynome.end()) {
                    it->second += c;
                    if (it->first != PTRef_Undef && it->second == 0)
                        polynome.erase(it);
                } else
                    polynome[t] = c;
            }
        }
    }

    if (polynome.find(PTRef_Undef) == polynome.end())
        polynome[PTRef_Undef] = 0;
    //
    // Canonize
    //
    if (do_canonize) {
        canonize();
    }
}

PTRef LAExpression::toPTRef() const {
    assert(polynome.find(PTRef_Undef) != polynome.end());
    assert(polynome.size() > 0);
    //
    // There is at least one variable
    //
    vec<PTRef> sum_list;
    opensmt::Real constant = 0;
    for (auto const & term: polynome) {
        if (term.first == PTRef_Undef) {
            constant = term.second;
        } else {
            PTRef coeff = logic.mkConst(term.second);
            PTRef vv = term.first;
            sum_list.push(logic.mkNumTimes(coeff, vv));
        }
    }
    if (sum_list.size() == 0) {
        sum_list.push(logic.getTerm_NumZero());
    }
    // Return in the form ax + by + ... = -c
    if (r == OP::EQ || r == OP::LEQ) {
        PTRef poly = logic.mkNumPlus(sum_list);
        constant = -constant;
        PTRef c = logic.mkConst(constant);
        if (r == OP::EQ) {
            return logic.mkEq(poly, c);
        } else {
            return logic.mkNumLeq(poly, c);
        }
    }
    // Return in the form ax + by + ... + c
    assert(r == OP::UNDEF);
    sum_list.push(logic.mkConst(constant));
    PTRef poly = logic.mkNumPlus(sum_list);
    return poly;
}

void LAExpression::print(ostream & os) const {
    assert(polynome.find(PTRef_Undef) != polynome.end());
    assert(polynome.size() > 0);
    if (r == OP::EQ)
        os << "(=";
    else if (r == OP::LEQ)
        os << "(<=";
    opensmt::Real constant = 0;
    if (polynome.size() == 1)
        os << " " << polynome.at(PTRef_Undef);
    else {
        // There is at least one variable
        os << " (+";
        for (auto const & term: polynome) {
            if (term.first == PTRef_Undef)
                constant = -term.second;
            else
                os << " (* " << term.second << " " << logic.printTerm(term.first) << ")";
        }
        os << ")";
    }
    if (r == OP::EQ || r == OP::LEQ)
        os << " " << constant << ")";
    os << '\n';
}

opensmt::pair<PTRef, PTRef> LAExpression::getSubst() {
    if (polynome.size() == 1) {
        assert(polynome.find(PTRef_Undef) != polynome.end());
        PTRef v1 = PTRef_Undef, v2 = PTRef_Undef;
        return {v1, v2};
    }
    // There is at least one variable
    // Solve w.r.t. first variable
    solve();
    vec<PTRef> sum_list;
    opensmt::Real constant = 0;
    PTRef var = PTRef_Undef;
    for (auto const & term: polynome) {
        if (term.first == PTRef_Undef) {
            constant = -term.second;
        } else {
            if (var == PTRef_Undef) {
                var = term.first;
                assert(term.second == 1);
            } else {
                opensmt::Real coeff = -term.second;
                PTRef c = logic.mkConst(coeff);
                PTRef vv = term.first;
                sum_list.push(logic.mkNumTimes(c, vv));
            }
        }
    }
    sum_list.push(logic.mkConst(constant));
    PTRef poly = logic.mkNumPlus(sum_list);
    return {var, poly};
}

//
// Solve w.r.t. first variable
// ex.
//
// 3*x + 2*y -1*z + 5 = 0
//
// 1*x + 2/3*y - 1/3*z + 5/3 = 0
//
// it modifies the polynome internally
//
PTRef LAExpression::solve() {
    assert(r == OP::EQ);
    assert(polynome.find(PTRef_Undef) != polynome.end());
    if (polynome.size() == 1) {
        assert(polynome.find(PTRef_Undef) != polynome.end());
        return PTRef_Undef;
    }
    //
    // Get first useful variable
    //
    auto it = polynome.begin();
    if (it->first == PTRef_Undef) it++;
    PTRef var = it->first;
    const opensmt::Real coeff = it->second;
    //
    // Divide polynome by coeff
    //
    for (auto & term: polynome) {
        term.second /= coeff;
    }
    assert(polynome[var] == 1);
    return var;
}

//
// Canonize w.r.t. first variable
// ex.
//
// 3*x + 2*y -1*z + 5 = 0
//
// 1*x + 2/3*y - 1/3*z + 5/3 = 0
//
// it modifies the polynome internally
//
void
LAExpression::canonize() {
    if (polynome.size() == 1) {
        assert(polynome.find(PTRef_Undef) != polynome.end());
        return;
    }
    // Get first useful variable
    auto it = polynome.begin();
    if (it->first == PTRef_Undef) it++;
    if (r == OP::LEQ) {
        const opensmt::Real abs_coeff = (it->second > 0 ? it->second : opensmt::Real(-it->second));
        for (auto & term: polynome) {
            term.second /= abs_coeff;
        }
    } else {
        const opensmt::Real coeff = it->second;
        for (auto & term: polynome) {
            term.second /= coeff;
        }
    }
    assert(isCanonized());
}

void LAExpression::addExprWithCoeff(const LAExpression & a, const opensmt::Real & coeff) {
    //
    // Iterate over expression to add
    //
    for (auto it = a.polynome.begin(); it != a.polynome.end(); ++it) {
        auto it2 = polynome.find(it->first);
        if (it2 != polynome.end()) {
            it2->second += coeff * it->second;
            if (it2->first != PTRef_Undef && it2->second == 0)
                polynome.erase(it2);
        } else
            polynome[it->first] = coeff * it->second;
    }
}
