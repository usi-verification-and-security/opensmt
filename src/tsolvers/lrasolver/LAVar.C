/*********************************************************************
 Author: Aliaksei Tsitovich <aliaksei.tsitovich@lu.unisi.ch>
 Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>
 Antti Hyvarinen <antti.hyvarinen@gmail.com>

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

#include "LAVar.h"

const char* const BoundT::names[3] = {"[L]", "[U]", "[N]"};

LAVar::LAVar(PTRef e, unsigned id)
        : e(e)
        , col_id(-1)
        , row_id(-1)
        , curr_ub(-1)
        , curr_lb(-1)
        , bounds(LABoundListRef_Undef)
        , poly(PolyRef_Undef)
        , occs(OccListRef_Undef)
{
    header.basic = 0;
    header.reloced = 0;
    header.skp = 0;
    header.id = id;
}


