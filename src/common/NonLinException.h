/*
*  Copyright (c) 2024, Konstantin Britikov <britikovki@gmail.com>
*
*  SPDX-License-Identifier: MIT
*/

#ifndef OPENSMT_NONLINEXCEPTION_H
#define OPENSMT_NONLINEXCEPTION_H

namespace opensmt {
class NonLinException : public std::runtime_error {
public:
    NonLinException(std::string_view const reason_) : runtime_error(std::string(reason_)) {
        msg = "Term " + std::string(reason_) + " is non-linear";
    }
    virtual char const * what() const noexcept override { return msg.c_str(); }

private:
    std::string msg;
};
}

#endif // OPENSMT_NONLINEXCEPTION_H
