/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/


#ifndef ANODE_H
#define ANODE_H

#include <errno.h>

enum attr_t { AT_SYM, AT_STR, AT_NUM, AT_DEC, AT_HEX, AT_BIN, AT_KEY, AT_NONE };

class Anode {
  public:
    attr_t type;
    char*  value;
    vector<Anode*> children;
    Anode(attr_t t, char* v, list<Anode*>* c) : type(t), value(v)
    {
        if (c == NULL) return;
        for (list<Anode*>::iterator it = c->begin(); it != c->end(); it++)
            children.push_back(*it);
    }
};

class IdNode {
  public:
    char*  name;
    list<int> value;
    IdNode( char* n, vector< string >* v ) : name( n )
    {
        if ( v == NULL ) return;
        for ( vector< string >::iterator it = v->begin(); it != v->end(); it++ ) {
            errno = 0;
            int int_v = strtol( (*it).c_str(), NULL, 10 );
            if ( errno != 0 ) {
                perror( "Conversion to integer" );
                break;
            }
            value.push_back( int_v );
        }
    }
};

#endif
