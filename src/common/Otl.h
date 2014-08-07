/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

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

//
// OpenSMT Template Library
//
#ifndef OTL_H
#define OTL_H

#include "Global.h"
#include "SolverTypes.h"

namespace __gnu_cxx
{
  // Hash function for pairs of integer
  template<>
  class hash< Pair( int ) >
  {
  public:
    size_t operator( )( const Pair( int ) & p ) const
    {
      return p.first ^ p.second;
    }
  };
  // Hash function for pairs of integer
  template<>
  class hash< Clause * >
  {
  public:
    size_t operator( )( Clause * c ) const
    {
      return (size_t)c;
    }
  };
}

struct strEq { inline bool operator( )( const char * s1, const char * s2 ) const { assert( s1 && s2 ); return strcmp( s1, s2 ) == 0; } };

#endif
