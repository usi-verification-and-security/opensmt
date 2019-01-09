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
    state = State::MPQ_ALLOCATED_AND_VALID;
    try_fit_word();
    if ( wordPartValid() )
        kill_mpq( );
    assert( isWellFormed( ) );
}

FastRational::FastRational(FastRational &&other) noexcept : state{other.state}, num{other.num}, den{other.den}  {
    if (other.mpqMemoryAllocated()) {
        std::swap(this->mpq, other.mpq);
        other.state = State::WORD_VALID;
    }
}
void FastRational::reset()
{
    kill_mpq(); state = State::WORD_VALID; num  = 0; den = 1;
}
void FastRational::print(std::ostream & out) const
{
//  const bool sign = num < 0;
    const bool sign = this->sign() < 0;
    if (wordPartValid()) {
        word abs_num = (sign?-num:num);
        if (den == 1) {
            out << (sign?"(- ":"") << abs_num << (sign?")":"");
        } else {
            out << "(/ " << (sign?"(- ":"") << abs_num << (sign?") ":" ") << den << ")";
        }
    } else {
        assert(mpqPartValid());
        mpq_class mpq_c( mpq );
        if ( sign ) mpq_c = -mpq_c;
        out << (sign?"(- ":"") << mpq_c << (sign?")":"");
    }
}
void FastRational::print_(std::ostream & out) const
{
    if (wordPartValid()) {
        if (den == 1) {
            out << num;
        } else {
            out << num << "/" << den;
        }
    } else {
        assert(mpqPartValid());
        out << mpq;
    }
}
std::string FastRational::get_str() const
{
    std::ostringstream os;
    print_(os);
    return os.str();
}