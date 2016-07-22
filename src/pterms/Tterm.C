#include "Tterm.h"

using namespace std;

Tterm::Tterm()
    : name("")
    , body(PTRef_Undef)
{
}

Tterm::~Tterm()
{
}

void
Tterm::addArg(PTRef arg)
{
    assert(arg != PTRef_Undef);
    args.push(arg);
}

void
Tterm::setName(string& _name)
{
    name = _name;
}

void
Tterm::setName(const char *_name)
{
    name = string(_name);
}

void
Tterm::setBody(PTRef _body)
{
    assert(_body != PTRef_Undef);
    body = _body;
}

vec<PTRef>&
Tterm::getArgs()
{
    return args;
}

string&
Tterm::getName()
{
    return name;
}

PTRef
Tterm::getBody()
{
    return body;
}

