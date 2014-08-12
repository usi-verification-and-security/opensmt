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
#include "Alloc.h"

typedef uint32_t SRef;

static const SRef SRef_Undef = -1;

enum SortType { S_EMPTY, S_ID, S_ID_LIST };

// What are these for?
enum DataType { SORT_ID_SIMPL, SORT_ID_REAL, SORT_ID_INT, SORT_ID_ARRAY, SORT_ID_COST, SORT_ID_BITVEC, SORT_ID_BOOL, SORT_ID_CMPLX, SORT_ID_UNDEF };
enum IdType   { IDTYPE_SIMPLE, IDTYPE_CMPLX };

class IdStr;
typedef RegionAllocator<uint32_t>::Ref IdStrRef;
const IdStrRef IdStr_Undef = RegionAllocator<uint32_t>::Ref_Undef;

class IdStr {
    char str[0];
  public:
    IdStr(const char* c) { int i; for (i = 0; *c != 0; i++) str[i] = *c; str[i] = 0; }
    int size() { return strlen(str); }
    const char* getName() { return str; }
};

class IdStrAllocator : public RegionAllocator<uint32_t>
{
    static int IdStrWord32Size(int size) {
        return (size+1) / sizeof(uint32_t) + ((size+1) % sizeof(uint32_t) == 0 ? 0 : 1); }
  public:
    IdStrAllocator() {}
    void moveTo(IdStrAllocator &to) {
        RegionAllocator<uint32_t>::moveTo(to); }
    IdStrRef alloc(const char* c)
    {
        IdStrRef sid = RegionAllocator<uint32_t>::alloc(IdStrWord32Size(strlen(c)));
        new (lea(sid)) IdStr(c);
        return sid;
    }
    IdStr&       operator[](Ref r)       { return (IdStr&)RegionAllocator<uint32_t>::operator[](r); }
    const IdStr& operator[](Ref r) const { return (IdStr&)RegionAllocator<uint32_t>::operator[](r); }
    IdStr*       lea       (Ref r)       { return (IdStr*)RegionAllocator<uint32_t>::lea(r); }
    Ref          ael       (const IdStr* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(IdStrRef sid)
    {
        IdStr& s = operator[](sid);
        RegionAllocator<uint32_t>::free(IdStrWord32Size(s.size()));
    }

    void reloc(IdStrRef&, IdStrAllocator&) { assert(false); }
};

class Identifier;
typedef RegionAllocator<uint32_t>::Ref IdRef;
const IdRef Id_Undef = RegionAllocator<uint32_t>::Ref_Undef;

class Identifier {
  private:
    IdStrRef      nr;
    IdType        type;
    vec<int>      numlist;

  public:
//    Identifier(ASTNode& IdNode);
    Identifier(IdStrRef name_) : nr(name_), type(IDTYPE_SIMPLE) {};
    Identifier(IdStrRef name_, vec<int>& nl) : nr(name_), type(IDTYPE_CMPLX) {
        for (int i = 0; i < nl.size(); i++) { numlist.push(nl[i]); }
    };
//    inline const std::string& toString() const { return name; };
    inline IdStrRef getNameRef() const { return nr; }
    inline IdType getType() const { return type; };
    int size() { return numlist.size(); }
};

class IdentifierAllocator : public RegionAllocator<uint32_t>
{
    IdStrAllocator isa;
    static int IdentifierWord32Size(int size) {
        return (sizeof(Identifier) + size) / sizeof(uint32_t); }
  public:
    IdentifierAllocator() {}
    void moveTo(IdStrAllocator &to) {
        RegionAllocator<uint32_t>::moveTo(to); }
    IdRef alloc(IdStrRef nr)
    {
        IdRef sid = RegionAllocator<uint32_t>::alloc(IdentifierWord32Size(0));
        new (lea(sid)) Identifier(nr);
        return sid;
    }
    IdRef alloc(IdStrRef nr, vec<int>& nl)
    {
        IdRef sid = RegionAllocator<uint32_t>::alloc(IdentifierWord32Size(nl.size()));
        new (lea(sid)) Identifier(nr, nl);
    }
    Identifier&       operator[](Ref r)       { return (Identifier&)RegionAllocator<uint32_t>::operator[](r); }
    const Identifier& operator[](Ref r) const { return (Identifier&)RegionAllocator<uint32_t>::operator[](r); }
    Identifier*       lea       (Ref r)       { return (Identifier*)RegionAllocator<uint32_t>::lea(r); }
    Ref               ael       (const Identifier* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(IdRef idr)
    {
        Identifier& s = operator[](idr);
        RegionAllocator<uint32_t>::free(IdentifierWord32Size(s.size()));
    }

    void reloc(IdRef&, IdentifierAllocator&) { assert(false); }
};




// Sort should most likely be a tree-like structure with references.  I don't
// like this implementation.
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
