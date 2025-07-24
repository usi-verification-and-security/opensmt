/*
 *  Copyright (c) 2025, Tomas Kolarik <tomaqa@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

namespace opensmt {

// Notify all solvers in the application to stop
void notifyGlobalStop();
void resetGlobalStop();
// Check if a global stop flag for all solvers has been triggered
bool globallyStopped();

} // namespace opensmt
