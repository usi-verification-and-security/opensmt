/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

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

#ifndef SSTORE_H
#define SSTORE_H

#include "SSort.h"
#include "SMTConfig.h"
#include "StringMap.h"
#include "Alloc.h"

class IdentifierStore
{
  private:
    StrAllocator<IdStr, IdStrRef> isa;
    IdentifierAllocator ia;
  public:
    // Provided for simplicity
    IdRef newIdentifier(const char* name) {
        IdStrRef nr = isa.alloc(name);
        return ia.alloc(nr);
    }
    IdRef newIdentifier(const char* name, vec<int>& nl) {
        IdStrRef nr = isa.alloc(name);
        return ia.alloc(nr, nl);
    }
    ~IdentifierStore() {}
    const char* getName(IdRef ir) { return isa[ia[ir].getNameRef()].getName(); }
    int* serializeIdentifiers() const;
    void deserializeIdentifiers(const int*);
};

class SStore
{
  private:
    IdentifierStore& is;
    StrAllocator<SStr, SStrRef> ssa;
    SortAllocator sa;
    Map<const char*,SRef,StringHash,Equal<const char*> > sortTable;
    vec<SRef>                                     sorts;
    vec<char*> sort_names; // Needed for deallocating the keys in sortTable
    typedef enum {      // These constants are stored on undo_stack_oper when
        SYMB            // A new symbol is created
      , PARA            // A new parameter
      , CONS            // An undoable cons is done
    } oper_t;

    SMTConfig & config; // Reference to config


  public:

    SStore(SMTConfig & c, IdentifierStore& is_) : is(is_), sa(ssa), config(c) { }

    ~SStore() {
        for (int i = 0; i < sort_names.size(); i++)
            free(sort_names[i]);
    }

    //===========================================================================
    // Public APIs for sort construction/destruction

    bool    contains        (const char* s)   const { return sortTable.contains(s); }
    SRef    operator []     (const char* s)   const { return sortTable[s]; }
    bool    contains        (const Sort& s)   const { return sortTable.contains(ssa[s.getNameRef()].getName()); }
    SRef    operator []     (const Sort& s) { return sortTable[ssa[s.getNameRef()].getName()]; }
    Sort*   operator []     (SRef sr)       { return &sa[sr]; }

    SRef    newSort         (IdRef id, vec<SRef>& rest);
    SRef    newSort         (IdRef id, const char* name, vec<SRef>& rest);
    bool    containsSort    (const char* name) const
        { bool rval = sortTable.contains(name); return rval; }
    const char* getName     (SRef sr) { return ssa[sa[sr].getNameRef()].getName(); }
    Sort&   getSort         (SRef sr) { return sa[sr]; }
    const vec<SRef>& getSorts() const { return sorts; }

    int*    serializeSorts() const;
    void    deserializeSorts(const int*);

    void dumpSortsToFile(ostream&);
};

#endif
