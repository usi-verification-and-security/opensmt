#include <unistd.h>
#include <sys/times.h>
#include "timer.hh"

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

static const double numTicksPerSec = (double)(sysconf(_SC_CLK_TCK));

Timer::Timer()
{
  reset();
}

void Timer::reset()
{
  struct tms clkticks;

  times(&clkticks);
  start_time =
    ((double) clkticks.tms_utime + (double) clkticks.tms_stime) /
    numTicksPerSec;
}


double Timer::get_duration()
{
  struct tms clkticks;

  times(&clkticks);
  double intermediate = 
    ((double) clkticks.tms_utime + (double) clkticks.tms_stime) /
    numTicksPerSec;
  return intermediate - start_time;
}

} // namespace bliss
