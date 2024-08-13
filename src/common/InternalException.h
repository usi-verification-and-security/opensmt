//
// Created by prova on 13.05.20.
//

#pragma once

#include <exception>
#include <string>

namespace opensmt {
class InternalException : public std::exception {
public:
    InternalException(std::string const & msg) : msg(msg) {}
    InternalException(char const * msg) : msg(msg) {}
    InternalException() : msg("Unknown internal error") {}
    virtual char const * what() const noexcept override { return msg.c_str(); }

private:
    std::string msg;
};
} // namespace opensmt
