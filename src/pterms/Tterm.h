#ifndef TTERM_H
#define TTERM_H

#include <iostream>

#include "SSort.h"
#include "SymStore.h"
#include "PtStore.h"

class Tterm
{
public:
    Tterm();
    ~Tterm();

    void addArg(PTRef);
    void setName(string&);
    void setName(const char*);
    void setBody(PTRef);

    vec<PTRef>& getArgs();
    string& getName();
    PTRef getBody();

private:
    std::string name;
    vec<PTRef> args;
    PTRef body;
};

#endif //TTERM_H
