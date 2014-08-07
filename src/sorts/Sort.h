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


#ifndef SORT_H
#define SORT_H
#include <string.h>
#include <sstream>
#include "minisat/mtl/Vec.h"
#include "parsers/smt2new/smt2newcontext.h"
//#include "logics/Logic.h"
#include "common/Global.h"
#include "common/IntTypes.h"

typedef uint32_t SRef;

static const SRef SRef_Undef = -1;

enum SortType { S_EMPTY, S_ID, S_ID_LIST };

// What are these for?
enum DataType { SORT_ID_SIMPL, SORT_ID_REAL, SORT_ID_INT, SORT_ID_ARRAY, SORT_ID_COST, SORT_ID_BITVEC, SORT_ID_BOOL, SORT_ID_CMPLX, SORT_ID_UNDEF };
enum IdType   { IDTYPE_SIMPLE, IDTYPE_CMPLX };

class Identifier {
  private:
    std::string   name;
    vec<int>      numlist;
    IdType        type;

  public:
    Identifier(ASTNode& IdNode);
    Identifier(std::string& name_) : name(name_), type(IDTYPE_SIMPLE) {};
    Identifier(std::string& name_, vec<int>& nl) : type(IDTYPE_CMPLX) {
        std::stringstream ss;
        ss << name_ << " ( ";
        for (int i = 0; i < nl.size(); i++) { numlist.push(nl[i]);  ss << nl[i] << " "; }
        ss << " )"; name = ss.str(); };
    Identifier(const char* name_) : name(name_), type(IDTYPE_SIMPLE) {};
    inline const std::string& toString() const { return name; };
    inline bool isPara () const { return false; };
    inline IdType getType() const { return type; };
};


// Sort should most likely be a tree-like structure with references.  I don't like this implementation.
class Sort {
  private:
    static sortid_t static_uniq_id;

    SortType    type;
    Identifier* id;
    vec<Sort*>  rest_sorts;
    DataType    stype;
    sortid_t    uniq_id;
    int         par_num;
    char*       canon_name;
  public:
    Sort(ASTNode& sn);
    Sort(Identifier& id, vec<Sort*>& rest);
    Sort(Identifier& id);

    string* toString();
    inline const char*   getCanonName () const { return canon_name;              };
    inline bool hasSortBool           () const { return stype == SORT_ID_BOOL;   };
    inline bool hasSortReal           () const { return stype == SORT_ID_REAL;   };
    inline bool hasSortInt            () const { return stype == SORT_ID_INT;    };
    inline bool hasSortArray          () const { return stype == SORT_ID_ARRAY;  };
    inline bool hasSortCost           () const { return stype == SORT_ID_COST;   };
    inline bool hasSortBitvec         () const { return stype == SORT_ID_BITVEC; };
    inline bool hasSortCmplx          () const { return stype == SORT_ID_CMPLX;  };
    inline bool hasSortUndef          () const { return stype == SORT_ID_UNDEF;  };

    inline Identifier*    getCar () const { return id;                      };
    inline Sort*          get2nd () const { return rest_sorts[0];           };
    inline Sort*          get3rd () const { return rest_sorts[1];           };
    inline bool           isPara () const { return false;                   };
    inline sortid_t       getId  () const { return uniq_id;                 };

    inline bool           isPredef() const { return false; }; // Check this from the logic instead?

    struct idLessThan
    {
      inline bool operator( )( Sort * x, Sort * y )
      {
        return (x->getId( ) <  y->getId( )); // Too shallow? What is this for?
//  	  || (x->getId( ) == y->getId( ) && x->getCdr( )->getId( ) < y->getCdr( )->getId( ) );
      }
    };

};

#endif // SORT_H
