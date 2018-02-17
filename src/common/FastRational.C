/*
Fast rationals
David Monniaux, VERIMAG 2008-2009

Copyright (c) 2008, 2009 Centre national de la recherche scientifique (CNRS)
 */

#include "FastRational.h"
#include <sstream>

//mpz_init(FastRational::one);
//mpz_set_si(FastRational::one, 1);


FastRational::FastRational( const char * s, const int base )
{
    mpq_init(mpq);
    mpq_set_str(mpq, s, base);
    mpq_canonicalize( mpq );
    has_mpq = true;
    make_word( );
    if ( has_word )
        kill_mpq( );

    assert( isWellFormed( ) );
}

FastRational::FastRational(FastRational &&other) {
    if(other.has_word) {
        this->has_word = true;
        this->has_mpq = false;
        this->num = other.num;
        this->den = other.den;
    }
    else{
        assert(other.has_mpq);
        this->has_mpq = true;
        this->has_word = false;
        other.has_mpq = false;
        std::swap(this->mpq, other.mpq);
    }
}

void FastRational::reset()
{
    kill_mpq(); has_mpq = false; has_word = true; num  = 0; den = 1;
}

void FastRational::print(std::ostream & out) const
{
//  const bool sign = num < 0;
    const bool sign = this->sign() < 0;
    if (has_word) {
        word abs_num = (sign?-num:num);
        if (den == 1) {
            out << (sign?"(- ":"") << abs_num << (sign?")":"");
        } else {
            out << "(/ " << (sign?"(- ":"") << abs_num << (sign?") ":" ") << den << ")";
        }
    } else {
        assert(has_mpq);
        mpq_class mpq_c( mpq );
        if ( sign ) mpq_c = -mpq_c;
            out << (sign?"(- ":"") << mpq_c << (sign?")":"");
    }
}

void FastRational::print_(std::ostream & out) const
{
    if (has_word) {
        if (den == 1) {
            out << num;
        } else {
            out << num << "/" << den;
        }
    } else {
        assert(has_mpq);
        out << mpq;
    }
}

std::string FastRational::get_str() const
{
    std::ostringstream os;
    print_(os);
    return os.str();
}

