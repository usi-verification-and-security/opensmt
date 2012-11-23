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
