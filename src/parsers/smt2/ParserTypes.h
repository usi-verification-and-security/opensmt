/*
 * These are helpers for the parser, not visible to the program
 */

#include "ANode.h"


class SpNode {
  public:
    enum attr_t type;
    char* value;
    SpNode( attr_t t, char* v ) : type(t), value(v) {}
};

class Attr {
  public:
    char*  name;
    Anode* attr;
    Attr( char* n, Anode* a ) : name(n), attr(a) {}
};
