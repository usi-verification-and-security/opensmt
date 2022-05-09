//
// Created by prova on 13.05.20.
//

#ifdef OSMT_ASSERT_EXCEPTION_H
#else
#define OSMT_ASSERT_EXCEPTION_H
#include "OsmtInternalException.h"

class OsmtAssertException : public OsmtInternalException {
    std::string msg;
public:
    explicit OsmtAssertException(const char * file, unsigned line, const std::string & message) :
            OsmtInternalException(message + " at " + file + ":" + std::to_string(line)) {}
};


#endif // OSMT_ASSERT_EXCEPTION_H