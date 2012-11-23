/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2009, Roberto Bruttomesso

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#ifndef BVSOLVER_H
#define BVSOLVER_H

#include "TSolver.h"
#include "BitBlaster.h"

class BVSolver : public OrdinaryTSolver
{
public:

   BVSolver ( const int
            , const char *
	    , SMTConfig &
	    , Egraph & 
	    , SStore &
	    , vector< Enode * > &
	    , vector< Enode * > &
	    , vector< Enode * > & );
  ~BVSolver ( );

  lbool               inform              ( Enode * );
  bool                assertLit           ( Enode *, bool = false );
  void                pushBacktrackPoint  ( );
  void                popBacktrackPoint   ( );
  bool                check               ( bool );
  bool                belongsToT          ( Enode * );
  void                computeModel        ( );

private:

  vector< Enode * > stack;
  BitBlaster *      B;
};

#endif
