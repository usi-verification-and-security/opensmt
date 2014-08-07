/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>
      , Aliaksei Tsitovich  <aliaksei.tsitovich@usi.ch>
      , Edgar Pek           <edgar.pek@usi.ch>

OpenSMT -- Copyright (C) 2008 - 2012, Roberto Bruttomesso

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

#ifndef DLRESCALE_H
#define DLRESCALE_H

#include "Global.h"
#include "Otl.h"
#include "Egraph.h"

class DLRescale
{
public:

  DLRescale( Egraph & egraph_, SMTConfig & config_ ) 
    : egraph            ( egraph_ ) 
    , config            ( config_ ) 
    , curr_constant_sum ( 0 )
  { }

  ~DLRescale( ) { }

  void doit ( Enode * );

private:

  Egraph &           egraph;
  SMTConfig &        config;
  Real               curr_constant_sum;
};

#endif
