/*
Fast rationals
David Monniaux, VERIMAG 2008-2009

Copyright (c) 2008, 2009 Centre national de la recherche scientifique (CNRS)
 */

#ifndef FAST_RATIONALS_H
#define FAST_RATIONALS_H

#define FR_NDEBUG 1

#include <iostream>
#include <string>
#include <sstream>
#include <string.h>
#include <cstddef>
#include <gmpxx.h>
#include <stdlib.h>
#include <errno.h>
#include <cassert>
#include <stdint.h>
#include <limits.h>

typedef int32_t  word;
typedef uint32_t uword;
typedef int64_t  lword;
typedef uint64_t ulword;
#define WORD_MIN  INT_MIN
#define WORD_MAX  INT_MAX
#define UWORD_MAX UINT_MAX

class MpzUnit
{
  private:
    mpz_t unit;
  public:
    MpzUnit() { mpz_init(unit); mpz_set_si(unit, 1); }
    const mpz_t& getUnit() const { return unit; }
};

class FastRational
{
  static const MpzUnit unit;
public:
  //
  // Constructors
  //

  FastRational( ) : has_mpq(false), has_word(true), num(0), den(1) { }

  FastRational( word x ) : has_mpq(false), has_word(true), num(x), den(1) { }

  FastRational(const char* s, const int base = 10);

  inline FastRational( const FastRational & );

  FastRational( const mpz_class & x )
  {
    if ( x.fits_sint_p( ) )
    {
      num = x.get_si( );
      den = 1;
      has_word = true;
      has_mpq = false;
    }
    else
    {
      mpq_init( mpq );
      mpq_set_num( mpq, x.get_mpz_t( ) );
      mpz_class tmp_den = 1;
      mpq_set_den( mpq, tmp_den.get_mpz_t( ) );
      has_word = false;
      has_mpq = true;
    }
  }
  //
  // Destroyer
  //
  ~FastRational( ) { kill_mpq(); }

  inline FastRational & operator=( const FastRational & );

private:

  void kill_mpq()
  {
    if (has_mpq)
    {
      mpq_clear(mpq);
      has_mpq = false;
    }
  }

  void make_mpq() {
    if (!has_mpq) {
      assert(has_word);
      mpq_init(mpq);
      has_mpq=true;
      mpz_set_si(mpq_numref(mpq), num);
      mpz_set_ui(mpq_denref(mpq), den);
    }
  }

  void force_make_mpq() const
  {
    const_cast<FastRational*>(this)->make_mpq();
  }

  void make_erase_mpq()
  {
    if (!has_mpq)
    {
      mpq_init(mpq);
      has_mpq=true;
    }
  }
  //
  // Tries to convert the current rational
  // stored in mpq into word/uword
  //
  void make_word()
  {
    assert( has_mpq );
    if ( mpz_fits_sint_p(mpq_numref(mpq))
      && mpz_fits_uint_p(mpq_denref(mpq)))
    {
      num = mpz_get_si(mpq_numref(mpq));
      den = mpz_get_ui(mpq_denref(mpq));
      has_word = true;
    }
    else
    {
      has_word = false;
    }
  }

  friend inline void addition            ( FastRational &, const FastRational &, const FastRational & );
  friend inline void subtraction         ( FastRational &, const FastRational &, const FastRational & );
  friend inline void multiplication      ( FastRational &, const FastRational &, const FastRational & );
  friend inline void division            ( FastRational &, const FastRational &, const FastRational & );

  friend inline void additionAssign      ( FastRational &, const FastRational & );
  friend inline void subtractionAssign   ( FastRational &, const FastRational & );
  friend inline void multiplicationAssign( FastRational &, const FastRational & );
  friend inline void divisionAssign      ( FastRational &, const FastRational & );

public:

  void print_details ( std::ostream & ) const;
  void print         ( std::ostream & ) const;

  inline double get_d  ( ) const;
  std::string   get_str( ) const;

  inline bool operator==(const FastRational& b) const;

  inline FastRational operator-() const;

private:

  inline FastRational(word n, uword d);

  void print_(std::ostream& out) const;
  static inline int compare(lword a, lword b) {
    if (a < b) return -1;
    else if (a > b) return 1;
    else return 0;
  }

  bool has_mpq, has_word;
  word num;
  uword den;
  mpq_t mpq;

public:

  inline int compare(const FastRational& b) const;
  inline int sign() const;

  bool operator< ( const FastRational & b ) const { return compare(b) < 0; }
  bool operator> ( const FastRational & b ) const { return compare(b) > 0; }
  bool operator<=( const FastRational & b ) const { return compare(b) <= 0; }
  bool operator>=( const FastRational & b ) const { return compare(b) >= 0; }
  bool operator!=( const FastRational & b ) const { return !(*this == b); }

  inline unsigned size() const;

  bool den_is_unit() const {
      if (has_word)
          return den == 1;
      else
          return mpq_denref(mpq) == unit.getUnit();
  }

  inline FastRational ceil( ) const
  {
    if (has_word)
    {
      word ret = (num > 0 ? (uword)num : (uword)(-num) ) / den;
      if ( num < 0 ) ret = -ret;
      else ++ret;
      return ret;
    }
    else
    {
      mpz_class q;
      mpz_cdiv_q ( q.get_mpz_t( )
	         , mpq_numref( mpq )
	         , mpq_denref( mpq ) );
      FastRational ret( q ); 
      return ret;
    }
  }

  inline FastRational floor( ) const
  {
    return ceil( ) - 1;
  }

  bool isWellFormed() const;

  FastRational operator+(const FastRational& b) const
  {
    FastRational dest;
    assert(isWellFormed());
    assert(b.isWellFormed());
    addition(dest, *this, b);
    assert(dest.isWellFormed());
    return dest;
  }

  FastRational operator-(const FastRational& b) const
  {
    FastRational dest;
    assert(isWellFormed());
    assert(b.isWellFormed());
    subtraction(dest, *this, b);
    assert(dest.isWellFormed());
    return dest;
  }

  FastRational operator*(const FastRational& b) const
  {
    FastRational dest;
    assert(isWellFormed());
    assert(b.isWellFormed());
    multiplication(dest, *this, b);
    assert(dest.isWellFormed());
    return dest;
  }

  FastRational operator/(const FastRational& b) const
  {
    FastRational dest;
    assert(isWellFormed());
    assert(b.isWellFormed());
    division(dest, *this, b);
    assert(dest.isWellFormed());
    return dest;
  }

  FastRational& operator+=(const FastRational& b)
  {
    assert(isWellFormed());
    assert(b.isWellFormed());
    additionAssign(*this, b);
    assert(isWellFormed());
    return *this;
  }

  FastRational& operator-=(const FastRational& b)
  {
    assert(isWellFormed());
    assert(b.isWellFormed());
    subtractionAssign(*this, b);
    assert(isWellFormed());
    return *this;
  }

  FastRational& operator*=(const FastRational& b)
  {
    assert(isWellFormed());
    assert(b.isWellFormed());
    multiplicationAssign(*this, b);
    assert(isWellFormed());
    return *this;
  }

  FastRational& operator/=(const FastRational& b)
  {
    assert(isWellFormed());
    assert(b.isWellFormed());
    divisionAssign(*this, b);
    assert(isWellFormed());
    return *this;
  }

  inline FastRational inverse() const;
/*
  size_t hash() const {
    if (has_word) {
      return djb2(num, den);
    } else {
      return djb2(mpz_get_si(mpq_numref(mpq)), mpz_get_si(mpq_denref(mpq)));
    }
  }
*/
  bool isZero() const {
    if (has_word) {
      return num==0;
    } else {
      return mpq_sgn(mpq)==0;
    }
  }
};

inline std::ostream & operator<<(std::ostream & out, const FastRational & r)
{
  r.print(out);
  return out;
}

inline FastRational::FastRational(const FastRational& x) {
  num = x.num;
  den = x.den;
  has_mpq = false;
  if (! (has_word = x.has_word)) {
    assert(x.has_mpq);
    has_mpq = true;
    mpq_init(mpq);
    mpq_set(mpq, x.mpq);
  }
}

inline FastRational& FastRational::operator=(const FastRational& x) {
  num = x.num;
  den = x.den;
  has_word = x.has_word;
  if (!has_word) {
    assert(x.has_mpq);
    if (!has_mpq) {
      mpq_init(mpq);
      has_mpq = true;
    }
    mpq_set(mpq, x.mpq);
  } else {
    if (has_mpq) {
      mpq_clear(mpq);
      has_mpq = false;
    }
  }
  return *this;
}

inline bool FastRational::operator==(const FastRational& b) const {
  if (has_word && b.has_word) {
    return num == b.num && den == b.den;
  }
  force_make_mpq();
  b.force_make_mpq();
  return mpq_equal(mpq, b.mpq);
}

inline FastRational FastRational::operator-() const {
  if (has_word && num > WORD_MIN) {
    return FastRational(-num, den);
  } else {
    force_make_mpq();
    FastRational x;
    x.has_word = false;
    x.has_mpq = true;
    mpq_init(x.mpq);
    mpq_neg(x.mpq, mpq);
    return x;
  }
}

inline int FastRational::compare(const FastRational& b) const {
  if (has_word && b.has_word) {
    if (b.den == den) {
      return compare(num, b.num);
    } else {
      return compare(lword(num)*b.den, lword(b.num)*den);
    }
  }
  force_make_mpq();
  b.force_make_mpq();
  return mpq_cmp(mpq, b.mpq);
}

inline int FastRational::sign() const {
  if (has_word) {
    if (num < 0) return -1;
    else if (num > 0) return 1;
    else return 0;
  } else {
    assert(has_mpq);
    return mpq_sgn(mpq);
  }
}

inline uword absVal(word x) {
  return x>=0 ? x : -x;
}

inline ulword absVal(lword x) {
  return x>=0 ? x : -x;
}

template<typename integer> integer gcd(integer a, integer b) {
  if (a==0) return b;
  if (b==0) return a;

  if (b > a) {
    integer c = a;
    a = b;
    b = c;
  }
  while(true) {
    integer r = a%b;
    if (r==0) return b;
    a = b;
    b = r;
  }
}

template<ulword> ulword gcd(ulword a, ulword b);
template<uword> uword gcd(uword a, uword b);

#define CHECK_WORD(var, value) \
  do { \
    lword tmp = value; \
    if (tmp < WORD_MIN/2 || tmp > WORD_MAX/2) { \
      goto overflow; \
    } \
    var = tmp;\
  } while(0)

#define CHECK_POSITIVE(value) \
  if (value < 1) abort()

#define CHECK_UWORD(var, value) \
  do { \
    CHECK_POSITIVE(value); \
    ulword tmp = value; \
    if (tmp > UWORD_MAX) { \
      goto overflow; \
    } \
    var = tmp;\
  } while(0)
#define COMPUTE_WORD(var, value) \
  word var; CHECK_WORD(var, value)

inline bool FastRational::isWellFormed() const
{
    return (  has_word || has_mpq )
        && ( !has_word || (den != 0 && gcd(absVal(num), den)==1) )
        && ( !has_mpq  || mpz_sgn(mpq_denref(mpq))!=0 );
}

inline FastRational::FastRational(word n, uword d) : has_mpq(false), has_word(true) {
  assert(d > 0);
  if (n == 0) {
    num = 0;
    den = 1;
  } else if (n > 0) {
    word common = gcd(uword(n), d);
    num = n/common;
    den = d/common;
  } else {
    word common = gcd(uword(-n), d);
    num = n/common;
    den = d/common;
  }
}


inline void addition(FastRational& dst, const FastRational& a, const FastRational& b){
  if (a.has_word && b.has_word) {
    if (b.num == 0) {
      dst.num = a.num;
      dst.den = a.den;
    } else if (a.num == 0) {
      dst.num = b.num;
      dst.den = b.den;
    } else if (b.den == 1) {
      CHECK_WORD(dst.num, lword(a.num) + lword(b.num)*a.den);
      dst.den = a.den;
    } else if (a.den == 1) {
      CHECK_WORD(dst.num, lword(b.num) + lword(a.num)*b.den);
      dst.den = b.den;
    } else {
      lword n = lword(a.num)*b.den + lword(b.num)*a.den;
      ulword d = ulword(a.den) * b.den;
      lword common = gcd(absVal(n), d);
      word zn;
      uword zd;
      if (common > 1) {
	CHECK_WORD(zn, n/common);
	CHECK_UWORD(zd, d/common);
      } else {
	CHECK_WORD(zn, n);
	CHECK_UWORD(zd, d);
      }
      dst.num = zn;
      dst.den = zd;
    }
    dst.kill_mpq();
    return;
  }

 overflow:
  a.force_make_mpq();
  b.force_make_mpq();
  dst.make_erase_mpq();
  mpq_add(dst.mpq, a.mpq, b.mpq);
  dst.make_word();
}

inline void subtraction(FastRational& dst, const FastRational& a, const FastRational& b){
  if (a.has_word && b.has_word) {
    if (b.num == 0) {
      dst.num = a.num;
      dst.den = a.den;
    } else if (a.num == 0) {
      dst.num = -b.num;
      dst.den = b.den;
    } else if (b.den == 1) {
      CHECK_WORD(dst.num, lword(a.num) - lword(b.num)*a.den);
      dst.den = a.den;
    } else if (a.den == 1) {
      CHECK_WORD(dst.num, -lword(b.num) + lword(a.num)*b.den);
      dst.den = b.den;
    } else {
      lword n = lword(a.num)*b.den - lword(b.num)*a.den;
      ulword d = ulword(a.den) * b.den;
      lword common = gcd(absVal(n), d);
      word zn;
      uword zd;
      if (common > 1) {
	CHECK_WORD(zn, n/common);
	CHECK_UWORD(zd, d/common);
      } else {
	CHECK_WORD(zn, n);
	CHECK_UWORD(zd, d);
      }
      dst.num = zn;
      dst.den = zd;
    }
    dst.kill_mpq();
    return;
  }

 overflow:
  a.force_make_mpq();
  b.force_make_mpq();
  dst.make_erase_mpq();
  mpq_sub(dst.mpq, a.mpq, b.mpq);
  dst.make_word();
}

inline void multiplication(FastRational& dst, const FastRational& a, const FastRational& b){
  if ((a.has_word && a.num==0) || (b.has_word && b.num==0)) {
    dst.num=0;
    dst.den=1;
    dst.has_word = true;
    dst.kill_mpq();
    return;
  }

  if (a.has_word && a.num==1 && a.den==1) {
    dst = b;
    return;
  }
  if (b.has_word && b.num==1 && b.den==1) {
    dst = a;
    return;
  }

  if (a.has_word && b.has_word) {
    word zn;
    uword zd;
    word common1 = gcd(absVal(a.num), b.den), common2 = gcd(a.den, absVal(b.num));
    lword k1, k2;
    ulword k3, k4; // Changed lword => ulword
    if (common1 > 1) {
      k1 = lword(a.num)/common1;
      k4 = ulword(b.den)/common1;
    } else {
      k1 = lword(a.num);
      k4 = ulword(b.den);
    }
    if (common2 > 1) {
      k2 = lword(b.num)/common2;
      k3 = ulword(a.den)/common2;
    } else {
      k2 = lword(b.num);
      k3 = ulword(a.den);
    }
    CHECK_WORD(zn, k1 * k2);
    CHECK_UWORD(zd, k3 * k4);
    dst.num = zn;
    dst.den = zd;
    dst.has_word = true;
    dst.kill_mpq();
    return;
  }

 overflow:
  a.force_make_mpq();
  b.force_make_mpq();
  dst.make_erase_mpq();
  mpq_mul(dst.mpq, a.mpq, b.mpq);
  dst.make_word();
}

inline void division(FastRational& dst, const FastRational& a, const FastRational& b){
  if (a.has_word && b.has_word) {
    word common1 = gcd(absVal(a.num), absVal(b.num));
    word common2 = gcd(a.den, b.den);
    word zn;
    uword zd;
    CHECK_WORD(zn, (lword(a.num)/common1) * (b.den/common2));
    CHECK_UWORD(zd, ulword(absVal(b.num)/common1) * (a.den/common2));
    dst.num = zn;
    dst.den = zd;
    if (b.num < 0) dst.num=-dst.num;
    dst.has_word = true;
    dst.kill_mpq();
    return;
  }

 overflow:
  a.force_make_mpq();
  b.force_make_mpq();
  dst.make_erase_mpq();
  mpq_div(dst.mpq, a.mpq, b.mpq);
  dst.make_word();
}

inline double FastRational::get_d() const {
  if (has_word) {
    return double(num)/double(den);
  } else {
    assert(has_mpq);
    return mpq_get_d(mpq);
  }
}

inline void additionAssign(FastRational& a, const FastRational& b){
  if (b.has_word) {
    if (b.num == 0) return;
    if (a.has_word) {
      if (b.den == 1) {
	CHECK_WORD(a.num, lword(a.num) + lword(b.num)*a.den);
      } else if (a.num == 0) {
	a.num = b.num;
	a.den = b.den;
      } else {
	lword n = lword(a.num)*b.den + lword(b.num)*a.den;
	ulword d = ulword(a.den) * b.den;
	lword common = gcd(absVal(n), d);
	word zn;
	uword zd;
	if (common > 1) {
	  CHECK_WORD(zn, n/common);
	  CHECK_UWORD(zd, d/common);
	} else {
	  CHECK_WORD(zn, n);
	  CHECK_UWORD(zd, d);
	}
	a.num = zn;
	a.den = zd;
      }
      a.kill_mpq();
      return;
    }
  }

 overflow:
  a.make_mpq();
  b.force_make_mpq();
  mpq_add(a.mpq, a.mpq, b.mpq);
  a.make_word();
}

inline void subtractionAssign(FastRational& a, const FastRational& b){
  if (a.has_word && b.has_word) {
    uword common = gcd(a.den, b.den);
    COMPUTE_WORD(n1, lword(a.num) * (b.den / common));
    COMPUTE_WORD(n2, lword(b.num) * (a.den / common));
    lword n = lword(n1) - lword(n2);
    ulword d = ulword(a.den) * (b.den / common);
    common = gcd(absVal(n), d);
    word zn;
    uword zd;
    CHECK_WORD(zn, n/common);
    CHECK_UWORD(zd, d/common);
    a.num = zn;
    a.den = zd;
    a.kill_mpq();
    return;
  }

 overflow:
  a.make_mpq();
  b.force_make_mpq();
  mpq_sub(a.mpq, a.mpq, b.mpq);
  a.make_word();
}

inline void multiplicationAssign(FastRational& a, const FastRational& b){
  if (a.has_word && b.has_word) {
    word common1 = gcd(absVal(a.num), b.den);
    word common2 = gcd(a.den, absVal(b.num));
    word zn;
    uword zd;
    CHECK_WORD(zn, lword(a.num/common1) * (b.num/common2));
    CHECK_UWORD(zd, ulword(a.den/common2) * (b.den/common1));
    a.num = zn;
    a.den = zd;
    a.kill_mpq();
    return;
  }

 overflow:
  a.make_mpq();
  b.force_make_mpq();
  mpq_mul(a.mpq, a.mpq, b.mpq);
  a.make_word();
}

inline void divisionAssign(FastRational& a, const FastRational& b){

  if (a.has_word && b.has_word) {
    word common1 = gcd(absVal(a.num), absVal(b.num)),
         common2 = gcd(a.den, b.den);

    assert( common1 != 0 );
    assert( common2 != 0 );

    word zn;
    uword zd;
    if (b.num < 0) {
      CHECK_WORD(zn, -lword(a.num/common1) * (b.den/common2));
    } else {
      CHECK_WORD(zn,  lword(a.num/common1) * (b.den/common2));
    }
    CHECK_UWORD(zd, ulword(absVal(b.num)/common1) * (a.den/common2));
    a.den = zd;
    a.num = zn;
    a.kill_mpq();
    return;
  }

 overflow:
  a.make_mpq();
  b.force_make_mpq();
  mpq_div(a.mpq, a.mpq, b.mpq);
  a.make_word();
}

inline unsigned FastRational::size() const {
  if (has_word) return 64;
  return mpz_sizeinbase(mpq_numref(mpq), 2) +
    mpz_sizeinbase(mpq_denref(mpq), 2);
}

inline FastRational FastRational::inverse() const {
  FastRational dest;

  if (has_word) {
    assert(num != 0);
    word zn;
    uword zd;
    if (num > 0) {
      CHECK_WORD(zn, den);
      CHECK_UWORD(zd, num);
    } else {
      CHECK_WORD(zn, -lword(den));
      CHECK_UWORD(zd, -lword(num));
    }
    dest.num = zn;
    dest.den = zd;
    return dest;
  }
 overflow:
  dest.has_word = false;
  force_make_mpq();
  dest.make_erase_mpq();
  mpq_inv(dest.mpq, mpq);
  return dest;
}

inline FastRational abs(const FastRational& x) {
  if (x.sign() >= 0) {
    return x;
  } else {
    return -x;
  }
}

inline FastRational FastRational_inverse(const FastRational& x) {
  return x.inverse();
}

#endif
