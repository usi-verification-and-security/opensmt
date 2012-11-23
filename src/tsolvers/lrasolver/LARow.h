/*********************************************************************
 Author: Aliaksei Tsitovich <aliaksei.tsitovich@usi.ch>,
         Roberto Bruttomesso <roberto.bruttomesso@unisi.ch>

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

#ifndef LAROW_H
#define LAROW_H

#include "LAArray.h"

struct LARowItem
{
  int key;
  int pos;
  Real * coef;

  LARowItem( int _key, int _pos, Real * _coef )
  {
    key = _key;
    pos = _pos;
    coef = _coef;
  }
};

class LARow: public LAArray<LARowItem>
{
public:
  int add( const int key, const int pos, Real * coef );
};

#endif
