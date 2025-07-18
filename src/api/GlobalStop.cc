/*
 *  Copyright (c) 2025, Tomas Kolarik <tomaqa@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

namespace opensmt {

namespace {
    bool globalStopFlag{false};
}

void notifyGlobalStop() {
    globalStopFlag = true;
}

bool globallyStopped() {
    return globalStopFlag;
}

} // namespace opensmt
