/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>
        Aliaksei Tsitovich <aliaksei.tsitovich@gmail.com>

OpenSMT2 -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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

#ifndef LA_H
#define LA_H

#include <pterms/PtStructs.h>
#include <logics/ArithLogic.h>
#include <common/Real.h>

#include <map>

namespace opensmt {

class LAExpression {
    ArithLogic & logic;

public:
    LAExpression(ArithLogic & l) : logic(l), r(OP::UNDEF) {
        polynome[PTRef_Undef] = 0;
    }

    LAExpression(ArithLogic & l, PTRef e, bool do_canonize) :
        logic(l),r(l.isNumEq(e) ? OP::EQ : (l.isLeq(e) ? OP::LEQ : OP::UNDEF)) {
        initialize(e, do_canonize);
    }

    LAExpression(ArithLogic & l, PTRef e) : LAExpression(l, e, true) {}

    inline bool isTrue() {
        return polynome.size() == 1 && (r == OP::EQ ? polynome[PTRef_Undef] == 0 : polynome[PTRef_Undef] >= 0);
    }

    inline bool isFalse() {
        return polynome.size() == 1 && (r == OP::EQ ? polynome[PTRef_Undef] != 0 : polynome[PTRef_Undef] < 0);
    }

    using polynome_t = std::map<PTRef, Real, std::greater<PTRef>>;

    void initialize(PTRef, bool canonize = true);      // Initialize
    PTRef solve();           // Solve w.r.t. some variable
    void canonize();           // Canonize (different from solve!)
    PTRef toPTRef(SRef sort) const;

    void print(std::ostream &) const;

    pair<PTRef, PTRef> getSubst();    // Get a valid substitution

    // Adds an expression to the current one multiplied by Real
    void addExprWithCoeff(const LAExpression &, const Real &);

    // Export iterator in order to allow external procedures to read the polynomes
    using iterator = polynome_t::iterator;
    using const_iterator = polynome_t::const_iterator;

    inline iterator begin() { return polynome.begin(); }

    inline iterator end() { return polynome.end(); }

    inline const_iterator begin() const { return polynome.begin(); }

    inline const_iterator end() const { return polynome.end(); }

    // We assume that the first coeffient is 1 or -1
    inline bool isCanonized() {
        if (polynome.size() == 1) return true;
        auto it = polynome.begin();
        if (it->first == PTRef_Undef) {
            ++it;
        }
        PTRef var = it->first;
        return polynome[var].isOne() || polynome[var] == -1;
    }

private:
    enum class OP : char {
        UNDEF, EQ, LEQ
    } ;

    polynome_t polynome;            // PTRef --> coefficient (NULL for constant)
    const OP r;                   // Arithmetic relation

    // Print overloading
    inline friend std::ostream & operator<<(std::ostream & os, LAExpression & p) {
        p.print(os);
        return os;
    }
};

}

#endif
