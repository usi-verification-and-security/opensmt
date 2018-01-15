/*********************************************************************
 Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
 Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

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

#include "Delta.h"

//
// Set Delta to 0
//
void Delta::reset()
{
    infinite = false;
    positive = true;
    r->reset();
    d->reset();
}

//
// prints the Delta
//
void Delta::print( ostream & out ) const
{
  if( isPlusInf( ) )
    out << "+inf";
  else if( isMinusInf( ) )
    out << "-inf";
  else
    out << R( ) << "|" << D( );
}

char* Delta::printValue() const
{
    char* out;
    if (isPlusInf())
        asprintf(&out, "+inf");
    else if (isMinusInf())
        asprintf(&out, "-inf");
    else
        asprintf(&out, "(%s | %s)",
                r->get_str().c_str(),
                d->get_str().c_str());
    return out;
}


