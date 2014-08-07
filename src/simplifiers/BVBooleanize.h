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

#ifndef BV_BOOLEANIZE_HH
#define BV_BOOLEANIZE_HH

#include "Global.h"
#include "Otl.h"
#include "Egraph.h"

class BVBooleanize
{
public:

  BVBooleanize ( Egraph & egraph_, SMTConfig & config_ )
   : egraph ( egraph_ )
   , config ( config_ )
  { }

  virtual ~BVBooleanize( ) { }

  Enode * doit      ( Enode * );              // Main routine

private:

  Enode * propagateExtract     ( Enode * );   // Propagate extractions
  Enode * propagateExtractRec  ( Enode * );   // Propagate extractions recursively
  Enode * propagateBoolcast    ( Enode * );   // Propagate Boolcasts
  Enode * propagateBoolcastRec ( Enode * );   // Propagate Boolcasts recursively
  Enode * replaceWithTypeCasts ( Enode * );   // Add boolcasts
  Enode * rewriteRules         ( Enode * );   // Apply some rewrite rules
  Enode * removeCasts          ( Enode * );   // Remove remaining casts 
                                              
  Egraph &    egraph;                         // Reference to Egraph
  SMTConfig & config;                         // Reference to Config
                                            
  map< enodeid_t, Enode * > extraction_cache; // Cache for extraction propagation
  map< enodeid_t, Enode * > boolcast_cache;   // Cache for boolcast propagation
};

#endif
