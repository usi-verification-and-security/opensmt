/*
*  Copyright (c) 2024, Konstantin Britikov <britikovki@gmail.com>
*
*  SPDX-License-Identifier: MIT
*/

#ifndef OPENSMT_NONLINEXCEPTION_H
#define OPENSMT_NONLINEXCEPTION_H

#include <stdexcept>

namespace opensmt {
class NonLinException : public std::runtime_error {
public:
    NonLinException(std::string_view const reason_) : runtime_error("Term " + std::string(reason_) + " is non-linear"){}
};
}

#endif // OPENSMT_NONLINEXCEPTION_H
