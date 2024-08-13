/*********************************************************************
 Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>
       , Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
       , Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

 OpenSMT2 -- Copyright (C) 2012 - 2015, Antti Hyvarinen
                           2008 - 2012, Roberto Bruttomesso

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

#ifndef DELTA_H
#define DELTA_H

#include <common/Real.h>

#include <iosfwd>

namespace opensmt {

//
// Class to keep the delta values and bounds values for the LAVar
//
class Delta {
private:
    Real r;     // main value
    Real d;     // delta to keep track of < / <= difference


    inline bool isLess(const Real & c) const;    //basic function to use in comparison with Real operator
    inline bool isGreater(const Real & c) const; //basic function to use in comparison with Real operator

public:

    // possible types of initial Delta values;
    inline Delta();                               // Same as Delta(UPPER)
    inline Delta(const Real & v);                // Constructor for Real delta
    inline Delta(const Real & v, const Real & d); // Constructor for Real delta with strict part
    inline Delta(Real && v, Real && d);          // Constructor for Real delta with strict part
    inline Delta(const Delta & a);               // Copy constructor
    inline ~Delta();                             // Destructor

    inline const Real & R() const;                // main value
    inline const Real & D() const;                // delta to keep track of < / <= difference
    inline bool hasDelta() const;                // TRUE is delta != 0
    void negate() {
        r.negate();
        d.negate();
    }

    void reset();

    inline Delta & operator=(const Delta & a);    //Assign operator
    inline Delta & operator=(Delta &&) noexcept;            // Move assign operator
    inline Delta(Delta &&);                      // Move constructor
    inline Delta(Real &&);                       // Move constructor from Real

    // Comparisons overloading
    inline friend bool operator<(const Delta & a, const Delta & b);

    inline friend bool operator<=(const Delta & a, const Delta & b);

    inline friend bool operator>(const Delta & a, const Delta & b);

    inline friend bool operator>=(const Delta & a, const Delta & b);

    inline friend bool operator==(const Delta & a, const Delta & b);

    inline friend bool operator!=(const Delta & a, const Delta & b);

    inline friend bool operator<(const Delta & a, const Real & c);

    inline friend bool operator<=(const Delta & a, const Real & c);

    inline friend bool operator>(const Delta & a, const Real & c);

    inline friend bool operator>=(const Delta & a, const Real & c);

    inline friend bool operator<(const Real & c, const Delta & a);

    inline friend bool operator<=(const Real & c, const Delta & a);

    inline friend bool operator>(const Real & c, const Delta & a);

    inline friend bool operator>=(const Real & c, const Delta & a);

    // Arithmetic overloadings
    Delta& operator+=(Delta const & b);
    Delta& operator+=(Delta && b);

    Delta& operator-=(Delta const & b);
    Delta& operator-=(Delta && b);

    inline friend Delta operator-(const Delta & a, const Delta & b);

    inline friend Delta operator+(const Delta & a, const Delta & b);

    inline friend Delta operator*(const Real & c, const Delta & a);

    inline friend Delta operator*(const Delta & a, const Real & c);

    inline friend Delta operator/(const Delta & a, const Real & c);

    void print(std::ostream & out) const;            // print the Delta
    char * printValue() const;

    inline friend std::ostream & operator<<(std::ostream & out, const Delta & b) {
        b.print(out);
        return out;
    }

};


// main value
inline const Real & Delta::R() const {
    return r;
}

// delta value (to keep track of < / <= difference)
inline const Real & Delta::D() const {
    return d;
}

bool Delta::hasDelta() const {
    return !D().isZero();
}

// Arithmetic operators definitions.
inline Delta& Delta::operator+=(const Delta & b) {
    this->r += b.R();
    this->d += b.D();
    return *this;
}

inline Delta& Delta::operator+=(Delta && b) {
    this->r += std::move(b.r);
    this->d += std::move(b.d);
    return *this;
}

inline Delta& Delta::operator-=(Delta const & b) {
    this->r -= b.R();
    this->d -= b.D();
    return *this;
}

inline Delta& Delta::operator-=(Delta && b) {
    this->r -= std::move(b.R());
    this->d -= std::move(b.D());
    return *this;
}

Delta operator-(const Delta & a, const Delta & b) {
    return Delta(a.R() - b.R(), a.D() - b.D());
}

Delta operator+(const Delta & a, const Delta & b) {
    return Delta(a.R() + b.R(), a.D() + b.D());
}

Delta operator*(const Real & c, const Delta & a) {
    return Delta(c * a.R(), c * a.D());
}

Delta operator*(const Delta & a, const Real & c) {
    return c * a;
}

Delta operator/(const Delta & a, const Real & c) {
    return Delta(a.R() / c, a.D() / c);
}

// Comparison operators definitions.
// Most are implemented via calls to basic operators.
//
bool operator<(const Delta & a, const Delta & b) {
    return (a.R() < b.R() || (a.R() == b.R() && a.D() < b.D()));
}

bool operator<=(const Delta & a, const Delta & b) {
    return !(b < a);
}

bool operator>(const Delta & a, const Delta & b) {
    return b < a;
}

bool operator>=(const Delta & a, const Delta & b) {
    return !(a < b);
}

bool operator==(const Delta & a, const Delta & b) {
    return (a.R() == b.R() && a.D() == b.D());
}

bool operator!=(const Delta & a, const Delta & b) {
    return !(a == b);
}

bool operator<(const Delta & a, const Real & c) {
    return a.isLess(c);
}

bool operator<=(const Delta & a, const Real & c) {
    return !(a > c);
}

bool operator>(const Delta & a, const Real & c) {
    return a.isGreater(c);
}

bool operator>=(const Delta & a, const Real & c) {
    return !(a < c);
}

bool operator<(const Real & c, const Delta & a) {
    return a > c;
}

bool operator<=(const Real & c, const Delta & a) {
    return a >= c;
}

bool operator>(const Real & c, const Delta & a) {
    return a < c;
}

bool operator>=(const Real & c, const Delta & a) {
    return a <= c;
}

//
// basic function to use in comparison with Real
//
bool Delta::isLess(const Real & c) const {
    return (R() < c || (R() == c && D() < 0));
}

//
// basic function to use in comparison with Real
//
bool Delta::isGreater(const Real & c) const {
    return (R() > c || (R() == c && D() > 0));
}

Delta::Delta() : r{0}, d{0} {}

//
// Constructor for Real delta
//
Delta::Delta(const Real & v) : r{v}, d{0} {}


//
// Constructor for Real delta with strict bit
//
Delta::Delta(const Real & v_r, const Real & v_d) : r{v_r}, d{v_d} {}

Delta::Delta(Real && v_r, Real && v_d) : r{std::move(v_r)}, d{std::move(v_d)} { }


//
// Copy constructor
//
Delta::Delta(const Delta & a) : r{a.r}, d{a.d} {}


// Assign operator
Delta & Delta::operator=(const Delta & a) {
    if (this != &a) {
        r = a.r;
        d = a.d;
    }
    return *this;
}

// move constructor
Delta::Delta(Delta && other) = default;

// move constructor from real
Delta::Delta(Real && other) : r{std::move(other)}, d{0} {}

// move assign
Delta & Delta::operator=(Delta && other) noexcept {
    this->r = std::move(other.r);
    this->d = std::move(other.d);
    return *this;
}

// Destructor
Delta::~Delta() = default;

}

#endif
