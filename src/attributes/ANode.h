/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT -- Copyright (C) 2012 - 2014 Antti Hyvarinen

OpenSMT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with OpenSMT. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/


#ifndef ANODE_H
#define ANODE_H

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
