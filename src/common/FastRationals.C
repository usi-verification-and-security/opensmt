/*
Fast rationals
David Monniaux, VERIMAG 2008-2009

Copyright (c) 2008, 2009 Centre national de la recherche scientifique (CNRS)
 */

#include "FastRationals.h"

#ifdef FAST_GCD
#ifdef PRECOMPUTED_GCD
struct precomputed_gcd_t {
  static const unsigned threshold = 1<<8;

  unsigned tab[threshold][threshold];

  static unsigned normal_gcd(unsigned a, unsigned b) {
    if(a==0) return b;
    if(b==0) return a;

    if (b > a) {
      uword c = a;
      a = b;
      b = c;
    }
    while(true) {
      uword r = a%b;
      if (r==0) return b;
      a = b;
      b = r;
    }
  }

  precomputed_gcd_t() {
    for(unsigned i=0; i<threshold; i++) {
      for(unsigned j=0; j<=i; j++) {
	tab[i][j] = tab[j][i] = normal_gcd(i, j);
      }
    }
  }

  unsigned gcd(unsigned a, unsigned b) const {
    return tab[a][b];
  }
} precomputed_gcd;
#endif

uword gcd(uword a, uword b) {
  if(a==0) return b;
  if(b==0) return a;

  if (b > a) {
    uword c = a;
    a = b;
    b = c;
  }
  while(true) {
#ifdef PRECOMPUTED_GCD
    if (a < precomputed_gcd_t::threshold) {
      return precomputed_gcd.gcd(a, b);
    }
#endif
    uword r = a%b;
    if (r==0) return b;
    a = b;
    b = r;
  }
}

ulword gcd(ulword a, ulword b) {
  if(a==0) return b;
  if(b==0) return a;

  if (b > a) {
    ulword c = a;
    a = b;
    b = c;
  }

  while(true) {
    if (a < (ulword(1) << 32)) {
      return gcd(uword(a), uword(b));
    }
    ulword r = a%b;
    if (r==0) return b;
    a = b;
    b = r;
  }
}
#endif

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

inline void FastInteger::print_details(std::ostream& out) const {
  out << "[";
  if (has_word) {
    out << "WORD(" << num << ")";
  }
  if (has_mpz) {
    out << "MPZ(" << mpz << ")";
  }
  out << "]";
}

void FastInteger::print(std::ostream& out) const {
  if (has_word) {
    out << num;
  } else {
    assert(has_mpz);
    out << mpz;
  }
}

std::string FastInteger::get_str() const {
  std::ostringstream os;
  print(os);
  return os.str();
}

void FastRational::print_details(std::ostream& out) const {
  out << "[";
  if (has_word) {
    out << "WORD(" << num << "/" << den << ")";
  }
  if (has_mpq) {
    out << "MPQ(" << mpq << ")";
  }
  out << "]";
}

void FastRational::print(std::ostream & out) const
{
//  const bool sign = num < 0;
  const bool sign = this->sign() < 0;
  if (has_word) {
    word abs_num = (sign?-num:num);
    if (den == 1) {
      out << (sign?"(~ ":"") << abs_num << (sign?")":"");
    } else {
      out << "(/ " << (sign?"(~ ":"") << abs_num << (sign?") ":" ") << den << ")";
    }
  } else {
    assert(has_mpq);
    mpq_class mpq_c( mpq );
    if ( sign ) mpq_c = -mpq_c;
    out << (sign?"(~ ":"") << mpq_c << (sign?")":"");
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
