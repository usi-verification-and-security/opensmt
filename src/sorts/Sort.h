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
#include "common/Global.h"
#include "common/IntTypes.h"
#include "Alloc.h"

// XXX The implementation of sorts is incomplete: the sort system should have
// sort symbols and concrete sorts the way pterms are constructed.  As a
// result, we only support "constant sorts" of arity 0

typedef RegionAllocator<uint32_t>::Ref SRef;
const SRef SRef_Undef = RegionAllocator<uint32_t>::Ref_Undef;

enum SortType { S_EMPTY, S_ID, S_ID_LIST };

// What are these for?
enum DataType { SORT_ID_SIMPL, SORT_ID_REAL, SORT_ID_INT, SORT_ID_ARRAY, SORT_ID_COST, SORT_ID_BITVEC, SORT_ID_BOOL, SORT_ID_CMPLX, SORT_ID_UNDEF };
enum IdType   { IDTYPE_SIMPLE, IDTYPE_CMPLX };

class IdStr;
typedef RegionAllocator<uint32_t>::Ref IdStrRef;
const IdStrRef IdStr_Undef = RegionAllocator<uint32_t>::Ref_Undef;

class SStr;
typedef RegionAllocator<uint32_t>::Ref SStrRef;
const IdStrRef SStr_Undef = RegionAllocator<uint32_t>::Ref_Undef;

class IdStr {
    char str[0];
  public:
    IdStr(const char* c) { int i; for (i = 0; *c != 0; i++, c++) str[i] = *c; str[i] = 0; }
    int size() { return strlen(str); }
    const char* getName() { return str; }
};

class SStr {
    char str[0];
  public:
    SStr(const char* c) { int i; for (i = 0; *c != 0; i++, c++) str[i] = *c; str[i] = 0; }
    int size() { return strlen(str); }
    const char* getName() const { return str; }
};

template<class T, class TR>
class StrAllocator : public RegionAllocator<uint32_t>
{
    static int StrWord32Size(int size) {
        return (size+1) / sizeof(uint32_t) + ((size+1) % sizeof(uint32_t) == 0 ? 0 : 1); }
  public:
    StrAllocator() {}
    void moveTo(StrAllocator &to) {
        RegionAllocator<uint32_t>::moveTo(to); }
    TR alloc(const char* c)
    {
        TR sid = RegionAllocator<uint32_t>::alloc(StrWord32Size(strlen(c)));
        new (lea(sid)) T(c);
        return sid;
    }
    T&       operator[](Ref r)       { return (T&)RegionAllocator<uint32_t>::operator[](r); }
    const T& operator[](Ref r) const { return (T&)RegionAllocator<uint32_t>::operator[](r); }
    T*       lea       (Ref r)       { return (T*)RegionAllocator<uint32_t>::lea(r); }
    Ref      ael       (const T* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(TR sid)
    {
        T& s = operator[](sid);
        RegionAllocator<uint32_t>::free(StrWord32Size(s.size()));
    }

    void reloc(TR&, StrAllocator&) { assert(false); }
};

class Identifier;
typedef RegionAllocator<uint32_t>::Ref IdRef;
const IdRef IdRef_Undef = RegionAllocator<uint32_t>::Ref_Undef;

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
    StrAllocator<IdStr, IdStrRef> isa;
    static int IdentifierWord32Size(int size) {
        return (sizeof(Identifier) + size) / sizeof(uint32_t); }
  public:
    IdentifierAllocator() {}
    void moveTo(IdentifierAllocator &to) {
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
        return sid;
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

//    SortType    type;
    IdRef       idr;
    sortid_t    uniq_id;
    SStrRef     canon_name;
    int         size;
    SRef        rest_sorts[0];
  public:
//    Sort(ASTNode& sn);
    Sort(IdRef idr_, sortid_t uniq_id_, SStrRef name, vec<SRef>& rest)
        : idr(idr_)
        , uniq_id(uniq_id_)
        , canon_name(name)
        , size(0)
    { for (int i = 0; i < rest.size(); i++) rest_sorts[i] = rest[i]; }
//    Sort(Identifier& id, vec<Sort*>& rest);
//    Sort(Identifier& id);

    SStrRef  getNameRef        () const { return canon_name; }
    SStrRef  getCanonNameRef   () const { return canon_name; }
    int      getSize           () const { return size; }

//    inline bool hasSortBool           () const { return stype == SORT_ID_BOOL;   };
//    inline bool hasSortReal           () const { return stype == SORT_ID_REAL;   };
//    inline bool hasSortInt            () const { return stype == SORT_ID_INT;    };
//    inline bool hasSortArray          () const { return stype == SORT_ID_ARRAY;  };
//    inline bool hasSortCost           () const { return stype == SORT_ID_COST;   };
//    inline bool hasSortBitvec         () const { return stype == SORT_ID_BITVEC; };
//    inline bool hasSortCmplx          () const { return stype == SORT_ID_CMPLX;  };
//    inline bool hasSortUndef          () const { return stype == SORT_ID_UNDEF;  };

    inline IdRef          getCar () const { return idr;                      };
//    inline Sort*          get2nd () const { return rest_sorts[0];           };
//    inline Sort*          get3rd () const { return rest_sorts[1];           };
//    inline bool           isPara () const { return false;                   };
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

/*
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
*/
class SortAllocator : public RegionAllocator<uint32_t>
{
    static sortid_t static_uniq_id;
    StrAllocator<SStr, SStrRef>& ssa;
    static int SortWord32Size(int size) {
        return (sizeof(Sort) + size) / sizeof(uint32_t); }
  public:
    SortAllocator(StrAllocator<SStr, SStrRef>& ssa_) : ssa(ssa_) {}
    void moveTo(SortAllocator &to) {
        RegionAllocator<uint32_t>::moveTo(to); }
    SRef alloc(IdRef idr, SStrRef nr, vec<SRef>& rest)
    {
        SRef sid = RegionAllocator<uint32_t>::alloc(SortWord32Size(rest.size()));
        new (lea(sid)) Sort(idr, static_uniq_id++, nr, rest);
        return sid;
    }
    Sort&       operator[](Ref r)       { return (Sort&)RegionAllocator<uint32_t>::operator[](r); }
    const Sort& operator[](Ref r) const { return (Sort&)RegionAllocator<uint32_t>::operator[](r); }
    Sort*       lea       (Ref r)       { return (Sort*)RegionAllocator<uint32_t>::lea(r); }
    Ref         ael       (const Sort* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(IdRef idr)
    {
        Sort& s = operator[](idr);
        RegionAllocator<uint32_t>::free(SortWord32Size(s.getSize()));
    }

    void reloc(IdRef&, IdentifierAllocator&) { assert(false); }
};



#endif // SORT_H
