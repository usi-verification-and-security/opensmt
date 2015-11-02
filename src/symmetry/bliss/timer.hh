#ifndef BLISS_TIMER_HH
#define BLISS_TIMER_HH

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

/** \internal
 * \brief A very simple wrapper class for measuring elapsed user+system time.
 */

class Timer
{
  double start_time;
public:
  /**
   * Create and start a new timer.
   */
  Timer();

  /**
   * Reset the timer.
   */
  void reset();

  /**
   * Get the user+system time (in seconds) elapsed since the creation or
   * the last reset() call of the timer.
   */
  double get_duration();
};

} // namespace bliss

#endif
