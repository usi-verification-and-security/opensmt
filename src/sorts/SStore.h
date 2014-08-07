/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                         2008 - 2012 Roberto Bruttomesso

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
