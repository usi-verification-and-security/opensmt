#include "Tterm.h"
#include <cstring>

using namespace std;

Tterm::Tterm()
    : name(NULL)
    , body(PTRef_Undef)
{
}

Tterm::~Tterm()
{
    free(name);
}

// It's possible that the lhs constructor has not been called before
// assignment if the instance is just placed into a vec.  The call to
// reset() clears the vec instance from garbage that might confuse the
// code later.
Tterm& Tterm::operator=(const Tterm& o)
{
    args.reset();
    if (o.name == NULL) {
        name = NULL;
    }
    else {
        name = (char*) malloc(strlen(o.name)+1);
        strcpy(name, o.name);
    }

    o.args.copyTo(args);
    body = o.body;
    return *this;
}

void
Tterm::addArg(PTRef arg)
{
    assert(arg != PTRef_Undef);
    args.push(arg);
}

void
Tterm::setName(std::string& _name)
{
    setName(_name.c_str());
}

void
Tterm::setName(const char *_name)
{
    name = (char*) malloc(strlen(_name)+1);
    strcpy(name, _name);
}

void
Tterm::setBody(PTRef _body)
{
    assert(_body != PTRef_Undef);
    body = _body;
}

const vec<PTRef>&
Tterm::getArgs() const
{
    return args;
}

const char*
Tterm::getName() const
{
    return name;
}

PTRef
Tterm::getBody() const
{
    return body;
}

