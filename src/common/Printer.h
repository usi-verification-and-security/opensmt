/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Seyedmasoud Asadzadeh <seyedmasoud.asadzadeh@usi.ch>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef PRINTER_H
#define PRINTER_H

#include "Timer.h"
#include <iostream>

namespace opensmt {

    namespace Color {
        enum Code {
            FG_DEFAULT = 39,
            FG_Black = 30,
            BG_Black = 40,
            FG_Red = 31,
            BG_Red = 41,
            FG_Green = 32,
            BG_Green = 42,
            FG_Yellow = 33,
            BG_Yellow = 43,
            FG_Blue = 34,
            BG_Blue = 44,
            FG_Magenta = 35,
            BG_Magenta = 45,
            FG_Cyan = 36,
            BG_Cyan = 46,
            FG_White = 37,
            BG_White = 47,
            FG_BrightBlack = 90,
            BG_BrightBlack = 100,
            FG_BrightRed = 91,
            BG_BrightRed = 101,
            FG_BrightGreen = 92,
            BG_BrightGreen = 102,
            FG_BrightYellow = 93,
            BG_BrightYellow = 103,
            FG_BrightBlue = 94,
            BG_BrightBlue = 104,
            FG_BrightMagenta = 95,
            BG_BrightMagenta = 105,
            FG_BrightCyan = 96,
            BG_BrightCyan = 106,
            FG_BrightWhite = 97,
            BG_BrightWhite = 107
        };
    }
}
#endif
