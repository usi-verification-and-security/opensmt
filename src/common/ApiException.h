//
// Created by Martin Blicha on 30.07.20.
//

#ifndef OPENSMT_APIEXCEPTION_H
#define OPENSMT_APIEXCEPTION_H

#include <stdexcept>

namespace opensmt {
class ApiException : public std::runtime_error {
public:
    ApiException(std::string const & msg) : std::runtime_error(msg) {}
    ApiException(char const * msg) : std::runtime_error(msg) {}
};
} // namespace opensmt

#endif // OPENSMT_APIEXCEPTION_H
