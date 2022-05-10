/*
 * Copyright (c) 2022, Antti Hyvarinen <antti.hyvarinen@gmail.com>
 * Copyright (c) 2022, Masoud Asadzade <masoud.asadzade@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

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