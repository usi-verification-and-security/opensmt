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
