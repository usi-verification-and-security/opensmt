//
// Created by prova on 13.05.20.
//

#pragma once

class OsmtInternalException : public std::exception {
    std::string msg;
public:
    OsmtInternalException(const std::string & msg) : msg(msg) {}
    OsmtInternalException(const char * msg) : msg(msg) {}
    OsmtInternalException() : msg("Unknown internal error") {}
    virtual const char* what() const noexcept override { return msg.c_str(); }
};


