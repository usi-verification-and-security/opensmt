/*
 *  Copyright (c) 2024, Martin Blicha <martin.blicha@gmail.com>
 *
 *  SPDX-License-Identifier: MIT
 *
 */

#ifndef ICOLOR_H
#define ICOLOR_H

#include <cassert>
#include <stdexcept>
#include <string>

namespace opensmt {

/**
 * Colors represent information about belonging to a partition when formula is partitioned into two parts: A and B
 *
 * For example we can represent information of a variable occurs only in the first partition, only in the second
 * partition, or both.
 */
enum class icolor_t : char { I_UNDEF = 0, I_A = 1, I_B = 2, I_AB = I_A | I_B, I_S = 4 };

inline constexpr icolor_t operator|(icolor_t f, icolor_t s) {
    return static_cast<icolor_t>(static_cast<std::underlying_type_t<icolor_t>>(f) |
                                 static_cast<std::underlying_type_t<icolor_t>>(s));
}

inline constexpr icolor_t operator&(icolor_t f, icolor_t s) {
    return static_cast<icolor_t>(static_cast<std::underlying_type_t<icolor_t>>(f) &
                                 static_cast<std::underlying_type_t<icolor_t>>(s));
}

inline std::string colorToString(icolor_t c) {
    switch (c) {
        case icolor_t::I_UNDEF:
            return "UNDEF";
        case icolor_t::I_A:
            return "A";
        case icolor_t::I_B:
            return "B";
        case icolor_t::I_AB:
            return "AB";
        case icolor_t::I_S:
            return "S";
        default:
            assert(false);
            throw std::logic_error("Unreachable");
    }
}

} // namespace opensmt

#endif // ICOLOR_H
