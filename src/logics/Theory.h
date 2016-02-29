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
#ifndef THEORY_H
#define THEORY_H

#include "Deductions.h"
#include "TermMapper.h"
#include "Logic.h"
#include "LRALogic.h"
#include "LRATHandler.h"
#include "UFTHandler.h"

class Theory
{
  protected:
    vec<DedElem> deductions;
    SMTConfig &  config;
  public:
    virtual Logic          &getLogic()              = 0;
    virtual TSolverHandler &getTSolverHandler()     = 0;
    virtual TSolverHandler *getTSolverHandler_new(vec<DedElem>&) = 0;
    virtual bool            simplify(PTRef, PTRef&) = 0;
    vec<DedElem>           &getDeductionVec()   { return deductions; }
    bool                    computeSubstitutions(PTRef, PTRef&);
    Theory(SMTConfig &c) : config(c) {}
    virtual ~Theory()                           {};
};

class LRATheory : public Theory
{
  private:
    LRALogic    lralogic;
    LRATHandler lratshandler;
  public:
    LRATheory(SMTConfig& c)
        : Theory(c)
        , lralogic(c)
        , lratshandler(c, lralogic, deductions)
    { }
    ~LRATheory() {};
    LRALogic&    getLogic()    { return lralogic; }
    LRATHandler& getTSolverHandler() { return lratshandler; }
    LRATHandler *getTSolverHandler_new(vec<DedElem> &d) { return new LRATHandler(config, lralogic, d); }
    bool simplify(PTRef, PTRef&); // Theory specific simplifications
};

class UFTheory : public Theory
{
  private:
    Logic      logic;
    UFTHandler tshandler;
  public:
    UFTheory(SMTConfig& c)
        : Theory(c)
        , logic(c)
        , tshandler(c, logic, deductions)
    { }
    ~UFTheory() {}
    Logic&       getLogic()             { return logic; }
    UFTHandler&  getTSolverHandler()    { return tshandler; }
    const UFTHandler& getTSolverHandler() const { return tshandler; }
    UFTHandler *getTSolverHandler_new(vec<DedElem>& d) { return new UFTHandler(config, logic, d); }
    bool simplify(PTRef, PTRef&);
};

#endif
