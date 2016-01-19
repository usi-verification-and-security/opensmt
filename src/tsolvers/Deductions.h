/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

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

#ifndef DEDUCTIONS_H
#define DEDUCTIONS_H

#include "SolverTypes.h"
struct SolverId {
    uint32_t id;
    bool operator== (const SolverId id2) const { return id == id2.id; }
    bool operator!= (const SolverId id2) const { return id != id2.id; }
};

static SolverId SolverId_Undef = {UINT32_MAX};

class SolverDescr
{
    protected:
        static uint32_t id_counter;
        const SolverId  id;
        const char*     name;
        const char*     description;


    public:
        SolverDescr(const char* name_, const char* desc_)
        : id({id_counter++})
        , name(name_)
        , description(desc_)
        {
            getSolverList().push(this);
        }
        static vec<SolverDescr*>& getSolverList() { static vec<SolverDescr*> options; return options; }

        operator SolverId    (void) const { return id; }
        operator const char* (void) const { return name; }
};


struct DedElem {
    DedElem(SolverId id, lbool p) : deducedBy(id), polarity(p) {}
    SolverId deducedBy;
    lbool    polarity;
    bool operator== (const lbool l) const { return l == polarity; }
    bool operator!= (const lbool l) const { return l != polarity; }
    bool operator== (const SolverId id) const { return id == deducedBy; }
    bool operator!=(const SolverId id) const { return id != deducedBy; }
};

//static DedElem DedElem_Undef = {SolverId_Undef, l_Undef};
static DedElem DedElem_Undef(SolverId_Undef, l_Undef);

#endif
