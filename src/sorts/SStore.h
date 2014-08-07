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

#include "Sort.h"
#include "SMTConfig.h"
//#include "SplayTree.h"
#include "ANode.h"
#include "common/StringMap.h"

class gSymbol
{
  private:
    char*      name;
    char*      canon_name;
    int        arity;
    char*      attrib;
  public:
    gSymbol(char* n, int ar, char* attr );
    gSymbol(ASTNode& n);
    inline bool        isPredef     () const { return false; };
    const char*        getCanonName () const;

};

class SStore
{
private:

    Map<const char*,SRef,StringHash,Equal<const char*> > sortTable;
    vec<SRef>                                     sorts;
    // Temporary hack to avoid mem management for sorts for now
    vec<Sort*>                                    SRefToSort;
public:

    SStore( SMTConfig & c ) : config ( c )
  {
  }

  ~SStore( )
  {
  }

  //===========================================================================
  // Public APIs for snode construction/destruction

  void     insertgSymbol    ( Identifier*, int, char* ); // Inserts a symbol
  void     insertgSymbol    ( gSymbol& );                // Inserts a symbol
  void     removegSymbol    ( Identifier*, int );        // Remove a symbol
  void     removegSymbol    ( gSymbol& );                // Remove a symbol
  gSymbol* lookupgSymbol    ( const char* name );        // Retrieve a symbol

  bool    contains        (const char* s)   const { return sortTable.contains(s); }
  SRef    operator []     (const char* s)   const { return sortTable[s]; }
  bool    contains        (const Sort& s)   const { return sortTable.contains(s.getCanonName()); }
  SRef    operator []     (const Sort& s) { return sortTable[s.getCanonName()]; }
  Sort*   operator []     (SRef sr)       { return SRefToSort[sr]; }

  void    insertStore     ( Sort* );                               // Insert node into the global store

  void dumpSortsToFile ( ostream & );

private:
  //
  // TODO: Defines the set of operations that can be performed and that should be undone
  //
  typedef enum {      // These constants are stored on undo_stack_oper when
      SYMB            // A new symbol is created
    , PARA            // A new parameter
    , CONS            // An undoable cons is done
  } oper_t;

  SMTConfig & config; // Reference to config

  //
  // Related to term creation
  //
  void    initializeStore ( );                                     // Initializes the store

};

#endif
