#include <cstdlib>
#include <cstdio>
#include "defs.hh"

/*
  Copyright (c) 2006-2011 Tommi Junttila
  Released under the GNU General Public License version 3.
  
  This file is part of bliss.
  
  bliss is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License version 3
  as published by the Free Software Foundation.
  
  bliss is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  
  You should have received a copy of the GNU General Public License
  along with Foobar.  If not, see <http://www.gnu.org/licenses/>.
*/


namespace bliss {

void
fatal_error(const char* fmt, ...)
{
  va_list ap;
  va_start(ap, fmt);
  fprintf(stderr,"Bliss fatal error: ");
  vfprintf(stderr, fmt, ap);
  fprintf(stderr, "\nAborting!\n");
  va_end(ap);
  exit(1);
}

}
