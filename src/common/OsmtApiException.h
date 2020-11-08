//
// Created by Martin Blicha on 30.07.20.
//

#ifndef OPENSMT_OSMTAPIEXCEPTION_H
#define OPENSMT_OSMTAPIEXCEPTION_H

#include <stdexcept>

class OsmtApiException : public std::runtime_error {
public:
    OsmtApiException(const std::string & msg) : std::runtime_error(msg) {}
    OsmtApiException(const char * msg) : std::runtime_error(msg) {}
};



#endif //OPENSMT_OSMTAPIEXCEPTION_H
