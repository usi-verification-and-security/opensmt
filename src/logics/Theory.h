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
#ifndef THEORY_H
#define THEORY_H

#include "Logic.h"

#include <tsolvers/UFTHandler.h>

#include <memory>

namespace opensmt {

struct PreprocessingContext {
    std::size_t frameCount {0};
    std::size_t preprocessedFrameAssertionsCount{0};
    bool perPartition {false};
};

class Theory
{
  protected:

    SMTConfig & config;

    Theory(SMTConfig &c) : config(c) { }

  public:

    virtual Logic          &getLogic()              = 0;
    virtual const Logic    &getLogic() const        = 0;
    virtual TSolverHandler &getTSolverHandler()     = 0;

    virtual PTRef preprocessBeforeSubstitutions(PTRef fla, PreprocessingContext const &) { return fla; }
    virtual PTRef preprocessAfterSubstitutions(PTRef, PreprocessingContext const &) = 0;
    virtual void afterPreprocessing(span<const PTRef>) {}

    virtual                ~Theory() = default;
};

class UFTheory : public Theory
{
  private:
    Logic &    uflogic;
    UFTHandler tshandler;
  public:
    UFTheory(SMTConfig & c, Logic & logic )
        : Theory(c)
        , uflogic(logic)
        , tshandler(c, uflogic)
    { }
    virtual Logic&            getLogic() override { return uflogic; }
    virtual const Logic&      getLogic() const override { return uflogic; }
    virtual UFTHandler&       getTSolverHandler() override  { return tshandler; }
    virtual const UFTHandler& getTSolverHandler() const { return tshandler; }
    virtual PTRef preprocessBeforeSubstitutions(PTRef, PreprocessingContext const &) override;
    virtual PTRef preprocessAfterSubstitutions(PTRef, PreprocessingContext const &) override;
};

}

#endif
