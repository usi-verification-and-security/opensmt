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

static inline size_t djb2(size_t a, size_t b) {
  return (a << 5) + a + b;
}

class FastInteger {
  bool has_mpz, has_word;
  word num;
  mpz_t mpz;

  void kill_mpz() {
    if (has_mpz) {
      mpz_clear(mpz);
      has_mpz = false;
    }
  }

  void make_mpz() {
    if (!has_mpz) {
      assert(has_word);
      mpz_init(mpz);
      has_mpz=true;
      mpz_set_si(mpz, num);
    }
  }

  void force_make_mpz() const {
    const_cast<FastInteger*>(this)->make_mpz();
  }

  void make_erase_mpz() {
    if (!has_mpz) {
      mpz_init(mpz);
      has_mpz=true;
    }
  }

  void make_word() {
    if (mpz_fits_sint_p(mpz)) {
      num = mpz_get_si(mpz);
      has_word = true;
    } else {
      has_word = false;
    }
  }

  inline void init_read_string(const char *s);

public:
  FastInteger(const char *s) {
    init_read_string(s);
  }

  FastInteger(const std::string& s) {
    init_read_string(s.c_str());
  }

  inline FastInteger           (const mpz_class & x);
  inline FastInteger           (const mpz_t x);
  inline FastInteger           (const FastInteger & x);
  inline FastInteger& operator=(const FastInteger & x);

  FastInteger() : has_mpz(false), has_word(true), num(0) {
  }

  ~FastInteger() {
    kill_mpz();
  }

  FastInteger(word x) : has_mpz(false), has_word(true), num(x) {
  }

  friend void inline addition      (FastInteger & dst, const FastInteger & a, const FastInteger & b);
  friend void inline subtraction   (FastInteger & dst, const FastInteger & a, const FastInteger & b);
  friend void inline multiplication(FastInteger & dst, const FastInteger & a, const FastInteger & b);
  friend void inline division      (FastInteger & dst, const FastInteger & a, const FastInteger & b);
  friend void inline divexact      (FastInteger & dst, const FastInteger & a, const FastInteger & b);
  friend void inline modulo        (FastInteger & dst, const FastInteger & a, const FastInteger & b);
  friend void lcm                  (FastInteger & dst, const FastInteger & a, const FastInteger & b);  
  friend void gcd                  (FastInteger & dst, const FastInteger & a, const FastInteger & b);

  friend void inline additionAssign      (FastInteger & a, const FastInteger & b);
  friend void inline subtractionAssign   (FastInteger & a, const FastInteger & b);
  friend void inline multiplicationAssign(FastInteger & a, const FastInteger & b);
  friend void inline divisionAssign      (FastInteger & a, const FastInteger & b);
  friend void inline divexactAssign      (FastInteger & a, const FastInteger & b);
  friend void inline moduloAssign        (FastInteger & a, const FastInteger & b);

  void print_details(std::ostream& out) const;
  void print_(std::ostream& out) const;
  void print(std::ostream& out) const;

  double get_d() const;
  std::string get_str() const;

  mpz_ptr get_mpz_t() const {
    force_make_mpz();
    const_cast<FastInteger*>(this)->has_word = false;
    return const_cast<mpz_ptr>(mpz);
  }

  inline bool operator==(const FastInteger& b) const;

  inline FastInteger operator-() const;

private:
  static inline int compare(lword a, lword b) {
    if (a < b) return -1;
    else if (a > b) return 1;
    else return 0;
  }

public:
  inline int compare(const FastInteger& b) const;
  inline int sign() const;

  bool operator<(const FastInteger& b) const {
    return compare(b) < 0;
  }

  bool operator>(const FastInteger& b) const {
    return compare(b) > 0;
  }

  bool operator<=(const FastInteger& b) const {
    return compare(b) <= 0;
  }

  bool operator>=(const FastInteger& b) const {
    return compare(b) >= 0;
  }

  bool operator!=(const FastInteger& b) const {
    return !(*this == b);
  }

  inline unsigned size() const;

  friend class FastRational;

  FastInteger operator+(const FastInteger& b) const {
    FastInteger dest;
    addition(dest, *this, b);
    return dest;
  }

  FastInteger operator++( ) {
    *this = *this + 1;
    return *this;
  }

  FastInteger operator-(const FastInteger& b) const {
    FastInteger dest;
    subtraction(dest, *this, b);
    return dest;
  }

  FastInteger operator*(const FastInteger& b) const {
    FastInteger dest;
    multiplication(dest, *this, b);
    return dest;
  }

  FastInteger operator/(const FastInteger& b) const {
    FastInteger dest;
    division(dest, *this, b);
    return dest;
  }

  FastInteger operator%(const FastInteger& b) const {
    FastInteger dest;
    modulo(dest, *this, b);
    return dest;
  }

  FastInteger& operator+=(const FastInteger& b) {
    additionAssign(*this, b);
    return *this;
  }

  FastInteger& operator-=(const FastInteger& b) {
    subtractionAssign(*this, b);
    return *this;
  }

  FastInteger& operator*=(const FastInteger& b) {
    multiplicationAssign(*this, b);
    return *this;
  }

  FastInteger& operator%=(const FastInteger& b) {
    moduloAssign(*this, b);
    return *this;
  }

  inline FastInteger& operator/=(const FastInteger& b) {
    divisionAssign(*this, b);
    return *this;
  }

  size_t hash() const {
    if (has_word) {
      return num;
    } else {
      return mpz_get_si(mpz);
    }
  }

  bool isZero() const {
    if (has_word) {
      return num==0;
    } else {
      return mpz_sgn(mpz)==0;
    }
  }
};

inline std::ostream& operator<<(std::ostream& out, const FastInteger& r) {
  r.print(out);
  return out;
}

class FastRational
{
public:
  //
  // Constructors
  //

  inline FastRational(const FastInteger& x);

  FastRational( ) : has_mpq(false), has_word(true), num(0), den(1) { }

  FastRational( word x ) : has_mpq(false), has_word(true), num(x), den(1) { }

  inline FastRational( const FastRational & );

  FastRational( const char * s, const int base = 10 );

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

  inline FastInteger get_num( ) const
  {
    if (has_word)
      return FastInteger(num);
    else
      return FastInteger(mpq_numref(mpq));
  }

  inline FastInteger get_den( ) const
  {
    if (has_word)
      return FastInteger(den);
    else
      return FastInteger(mpq_denref(mpq));
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

  size_t hash() const {
    if (has_word) {
      return djb2(num, den);
    } else {
      return djb2(mpz_get_si(mpq_numref(mpq)), mpz_get_si(mpq_denref(mpq)));
    }
  }

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

inline FastRational inverse(const FastRational& a) {
  return a.inverse();
}

inline int sign(const FastRational& x) {
  return x.sign();
}

namespace std {

  template <typename object> struct hash;

  template<> struct hash<FastInteger> {
    size_t operator()(const FastInteger& x) {
      return x.hash();
    }
  };

  template<> struct hash<FastRational> {
    size_t operator()(const FastRational& x) {
      return x.hash();
    }
  };
}

inline void FastInteger::init_read_string(const char *s) {
  errno = 0;
  num = strtol(s, 0, 10);
  if (errno != ERANGE) {
    has_word = true;
    has_mpz = false;
  } else {
    has_word = false;
    mpz_init_set_str(mpz, s, 10);
    has_mpz = true;
  }
}

inline FastInteger::FastInteger(const mpz_class& x) {
  if (mpz_fits_sint_p(x.get_mpz_t())) {
    num = mpz_get_si(x.get_mpz_t());
    has_word = true;
    has_mpz = false;
  } else {
    has_word = false;
    has_mpz = true;
    mpz_init_set(mpz, x.get_mpz_t());
  }
}

inline FastInteger::FastInteger(const mpz_t x) {
  if (mpz_fits_sint_p(x)) {
    num = mpz_get_si(x);
    has_word = true;
    has_mpz = false;
  } else {
    has_word = false;
    has_mpz = true;
    mpz_init_set(mpz, x);
  }
}

inline FastInteger::FastInteger(const FastInteger& x) {
  num = x.num;
  has_word = x.has_word;
  if ( (has_mpz = x.has_mpz) ) {
    mpz_init(mpz);
    mpz_set(mpz, x.mpz);
  }
}

inline FastInteger& FastInteger::operator=(const FastInteger& x) {
  num = x.num;
  has_word = x.has_word;
  if (x.has_mpz) {
    if (! has_mpz) {
      mpz_init(mpz);
      has_mpz = true;
    }
    mpz_set(mpz, x.mpz);
  } else {
    if (has_mpz) {
      mpz_clear(mpz);
      has_mpz = false;
    }
  }
  return *this;
}

inline bool FastInteger::operator==(const FastInteger& b) const {
  if (has_word && b.has_word) {
    return num == b.num;
  }
  force_make_mpz();
  b.force_make_mpz();
  return mpz_cmp(mpz, b.mpz)==0;
}

inline FastInteger FastInteger::operator-() const {
  if (has_word && num > WORD_MIN) {
    return FastInteger(-num);
  } else {
    force_make_mpz();
    FastInteger x;
    x.has_word = false;
    x.has_mpz = true;
    mpz_init(x.mpz);
    mpz_neg(x.mpz, mpz);
    return x;
  }
}

inline int FastInteger::compare(const FastInteger& b) const {
  if (has_word && b.has_word) {
    return compare(num, b.num);
  }
  force_make_mpz();
  b.force_make_mpz();
  return mpz_cmp(mpz, b.mpz);
}

inline int FastInteger::sign() const {
  if (has_word) {
    if (num < 0) return -1;
    else if (num > 0) return 1;
    else return 0;
  } else {
    assert(has_mpz);
    return mpz_sgn(mpz);
  }
}

inline FastRational::FastRational(const FastInteger& x) {
  if (x.has_word) {
    num = x.num;
    den = 1;
    has_word = true;
    has_mpq = false;
  } else {
    assert(x.has_mpz);
    has_word = false;
    has_mpq = true;
    mpq_init(mpq);
    mpz_set(mpq_numref(mpq), x.mpz);
  }
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

#ifdef FAST_GCD
uword gcd(uword a, uword b);
ulword gcd(ulword a, ulword b);

#else
#ifdef BINARY_GCD
template<typename integer> integer gcd(integer a, integer b) {
  if(a==0) return b;
  if(b==0) return a;

  if (a > b) {
    a = a%b;
  } else if (a < b) {
    b = b%a;
  } else return a;

  if(a==0) return b;
  if(b==0) return a;

  unsigned shift=0;
  while((a&1)==0 && (b&1)==0) {
    a>>=1;
    b>>=1;
    shift++;
  }
  while((a&1)==0) a>>=1;

  while(b>0) {
    while((b&1)==0) b>>=1;
    if (b>a) {
      b-=a;
    } else {
      integer d=a-b;
      a=b;
      b=d;
    }
  }

  return a<<shift;
}
template<ulword> ulword gcd(ulword a, ulword b);
template<uword> uword gcd(uword a, uword b);

#else
template<typename integer> integer gcd(integer a, integer b) {
  if(a==0) return b;
  if(b==0) return a;

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
#endif
#endif

#define CHECK_WORD(var, value) \
  do { \
    lword tmp = value; \
    if (tmp < WORD_MIN/2 || tmp > WORD_MAX/2) { \
      goto overflow; \
    } \
    var = tmp;\
  } while(0)

#ifdef FR_NDEBUG
#define CHECK_POSITIVE(value)
#else
#define CHECK_POSITIVE(value) \
  if (value < 1) abort()
#endif

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
#define COMPUTE_UWORD(var, value) \
  uword var; CHECK_UWORD(var, value)

#define INTEGER_OP(name, op, mpzop) \
inline void name(FastInteger& dst, const FastInteger& a, const FastInteger& b){ \
  if (a.has_word && b.has_word) { \
    word zn; \
    CHECK_WORD(zn, lword(a.num) op lword(b.num)); \
    dst.num = zn; \
    return ; \
  } \
overflow: \
  a.force_make_mpz(); \
  b.force_make_mpz(); \
  dst.make_erase_mpz(); \
  mpz_##mpzop(dst.mpz, a.mpz, b.mpz); \
  dst.make_word(); \
} \
\
inline void name##Assign(FastInteger& a, const FastInteger& b){ \
  if (a.has_word && b.has_word) { \
    word zn; \
    CHECK_WORD(zn, lword(a.num) op lword(b.num)); \
    a.num = zn; \
    a.kill_mpz( ); \
    return ; \
  } \
overflow: \
  a.make_mpz(); \
  b.force_make_mpz(); \
  mpz_##mpzop(a.mpz, a.mpz, b.mpz); \
  a.make_word(); \
}

INTEGER_OP(addition, +, add)
INTEGER_OP(subtraction, -, sub)
INTEGER_OP(multiplication, *, mul)
INTEGER_OP(division, /, cdiv_q)
INTEGER_OP(modulo, %, cdiv_r)
INTEGER_OP(divexact, /, divexact)

inline void lcm(FastInteger& dst, const FastInteger& a, const FastInteger& b){
  if (a.has_word && b.has_word) {
    word zn;
    uword aAbs = absVal(a.num), bAbs = absVal(b.num);
    CHECK_WORD(zn, (ulword(aAbs / gcd(aAbs, bAbs)))*bAbs);
    dst.num = zn;
    dst.kill_mpz();
    return ;
  }
overflow:
  a.force_make_mpz();
  b.force_make_mpz();
  dst.make_erase_mpz();
  mpz_lcm(dst.mpz, a.mpz, b.mpz);
  dst.make_word();
}

inline void gcd(FastInteger& dst, const FastInteger& a, const FastInteger& b){
  if (a.has_word && b.has_word) {
    dst.num = gcd(absVal(a.num), absVal(b.num));
    dst.kill_mpz();
    return ;
  }

  a.force_make_mpz();
  b.force_make_mpz();
  dst.make_erase_mpz();
  mpz_gcd(dst.mpz, a.mpz, b.mpz);
  dst.make_word();
}

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
    lword k1, k2, k3, k4;
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

inline unsigned FastInteger::size() const {
  if (has_word) return 32;
  return mpz_sizeinbase(mpz, 2);
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

#if 0
inline FastRational::operator mpq_class() const {
  if (has_word) {
    return mpq_class(num)/den;
  } else {
    assert(has_mpq);
    return mpq_class(mpq);
  }
}

inline FastRational::FastRational(double x) {
  has_word = false;
  has_mpq = true;
  mpq_init(mpq);
  mpq_set_d(mpq, x);
  make_word();
}
#endif

inline FastInteger abs(const FastInteger& x) {
  if (x.sign() >= 0) {
    return x;
  } else {
    return -x;
  }
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
