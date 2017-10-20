/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2016 Antti Hyvarinen
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

#ifndef OPENSMT_CNFSTATE_H
#define OPENSMT_CNFSTATE_H

#include "PTRef.h"
#include "SolverTypes.h"

//---------------------------------------------------------------------------------------
// State for CNFs and mappings for terms
//
//
// Struct for communicating the cnf and the mapping between variables and PTRefs
//

struct VarPtPair
{
    Var v;
    PTRef tr;
};

class CnfState
{
    char*               cnf;
    vec<VarPtPair>      map;
    bool                unsat;
public:
    CnfState() : cnf(NULL), unsat(false) {};
    ~CnfState() { free(cnf); }
    void                  setUnsat()            { assert(cnf == NULL); unsat = true; }
    const char*           getCnf()              { return unsat ? "1 -1 0" : (cnf == NULL ? "c empty" : cnf); }
    void                  setCnf(char* cnf_)    { cnf = cnf_; }
    const vec<VarPtPair>& getMap()              { return map; }
    void                  addToMap(VarPtPair p) { map.push(p); }
};

#endif //OPENSMT_CNFSTATE_H
