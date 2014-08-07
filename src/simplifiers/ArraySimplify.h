/*********************************************************************
Author: Simone Fulvio Rollini <simone.rollini@gmail.com>

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
#ifndef ARRAYSIMPLIFY_H
#define ARRAYSIMPLIFY_H

#include "Global.h"
#include "Otl.h"
#include "Egraph.h"

class ArraySimplify
{
public:

  ArraySimplify( Egraph & egraph_, SMTConfig & config_ )
   : egraph  ( egraph_ )
   , config  ( config_ )
  { }

  virtual ~ArraySimplify( ) { }

  Enode * doit ( Enode * ); // Main routine

private:
  
  list< Enode * >             new_clauses;

  Egraph &    egraph;       // Reference to Egraph
  SMTConfig & config;       // Reference to Config

  void    preprocArrowUp ( );
  void    preprocIdx     ( Enode * );
  Enode * flattening     ( Enode * );
  Enode * simp1          ( Enode *, bool & );
  Enode * simp2          ( Enode *, bool & );
  Enode * simp3          ( Enode *, bool & );
};

#endif 
