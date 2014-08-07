/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2008 - 2012 Roberto Bruttomesso

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

#ifndef ENODE_TYPES_H
#define ENODE_TYPES_H

#include "SolverTypes.h"
#include "Global.h"
#include "Snode.h"
#include "sorts/Sort.h"

//
// IMPORTANT: CHANGE THESE VALUES ONLY IF YOU KNOW WHAT YOU ARE DOING !!!
// IMPORTANT: CHANGE THESE VALUES ONLY IF YOU KNOW WHAT YOU ARE DOING !!!
// IMPORTANT: CHANGE THESE VALUES ONLY IF YOU KNOW WHAT YOU ARE DOING !!!
//
// Predefined list of identifiers to allow
// fast term creation for common operators
// Except for extract, which is created
// on demand
//
#define ENODE_ID_UNDEF	          (-1)
#define ENODE_ID_ENIL	           (0)
#define ENODE_ID_TRUE              (1)
#define ENODE_ID_FALSE             (2)
#define ENODE_ID_NOT               (3)
#define ENODE_ID_IMPLIES           (4)
#define ENODE_ID_AND               (5)
#define ENODE_ID_OR                (6)
#define ENODE_ID_XOR               (7)
#define ENODE_ID_EQ	           (8)
#define ENODE_ID_ITE               (9)
#define ENODE_ID_DISTINCT         (10)
#define ENODE_ID_PLUS		  (11)
#define ENODE_ID_MINUS	          (12)
#define ENODE_ID_UMINUS	          (13)
#define ENODE_ID_TIMES	          (14)
#define ENODE_ID_DIV		  (15)
#define ENODE_ID_LEQ	          (16)
#define ENODE_ID_GEQ	          (17)
#define ENODE_ID_LT	          (18)
#define ENODE_ID_GT	          (19)
#define ENODE_ID_STORE	          (20)
#define ENODE_ID_SELECT	          (21)
#define ENODE_ID_CTINCUR          (22)
#define ENODE_ID_CTBOUND          (23)
#define ENODE_ID_DIFF             (24)
#define ENODE_ID_FAKE_INTERP      (25)
/*
#define ENODE_ID_BVSLT            (22)
#define ENODE_ID_BVSGT            (23)
#define ENODE_ID_BVSLE            (24)
#define ENODE_ID_BVSGE            (25)
#define ENODE_ID_BVULT            (26)
#define ENODE_ID_BVUGT            (27)
#define ENODE_ID_BVULE            (28)
#define ENODE_ID_BVUGE            (29)
#define ENODE_ID_CONCAT           (30)
#define ENODE_ID_BVAND            (31)
#define ENODE_ID_BVOR             (32)
#define ENODE_ID_BVXOR            (33)
#define ENODE_ID_BVNOT            (34)
#define ENODE_ID_BVADD            (35)
#define ENODE_ID_BVSUB            (36)
#define ENODE_ID_BVMUL            (37)
#define ENODE_ID_BVNEG            (38)
#define ENODE_ID_BVLSHR           (39)
#define ENODE_ID_BVASHR           (40)
#define ENODE_ID_BVSHL            (41)
#define ENODE_ID_BVSREM           (42)
#define ENODE_ID_BVUREM           (43)
#define ENODE_ID_BVSDIV           (44)
#define ENODE_ID_BVUDIV           (45)
#define ENODE_ID_ZERO_EXTEND      (46)
#define ENODE_ID_CBE              (47)
#define ENODE_ID_WORD1CAST        (48)
#define ENODE_ID_BOOLCAST         (49)
*/
//                                
// IMPORTANT:
// This must be equal to the last predefined ID
// it is used to check whether a function symbol
// is predefined or uninterpreted
//
#define ENODE_ID_LAST		  (24)

//
// Properties stored in integers
//  31       28 27 26                20 19       16 15                                            0
// |EE|EE|EE|EE|NN|AA|AA|AA|AA|AA|AA|AA|TT|TT|TT|TT|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|WW|
//   
// |<- etype ->|<------ arity -------->|<- dtype ->|<------------------ width -------------------->|
//
// Enode types
enum etype_t 
{ 
   ETYPE_UNDEF   = 0x00000000 // 0000 0000 0000 0000 0000 0000 0000 0000
 , ETYPE_SYMB    = 0x10000000 // 0001 0000 0000 0000 0000 0000 0000 0000
 , ETYPE_NUMB    = 0x20000000 // 0010 0000 0000 0000 0000 0000 0000 0000
 , ETYPE_LIST    = 0x30000000 // 0011 0000 0000 0000 0000 0000 0000 0000
 , ETYPE_TERM    = 0x40000000 // 0100 0000 0000 0000 0000 0000 0000 0000
 , ETYPE_DEF     = 0x50000000 // 0101 0000 0000 0000 0000 0000 0000 0000
};

#define ETYPE_MASK  0xF0000000 // 1111 0000 0000 0000 0000 0000 0000 0000
#define ARITY_N     0x08000000 // 0000 1000 0000 0000 0000 0000 0000 0000
#define ARITY_MASK  0x07F00000 // 0000 0111 1111 0000 0000 0000 0000 0000
#define DTYPE_MASK  0x000F0000 // 0000 0000 0000 1111 0000 0000 0000 0000
#define WIDTH_MASK  0x0000FFFF // 0000 0000 0000 0000 1111 1111 1111 1111
#define MAX_WIDTH   (WIDTH_MASK) 
#define ARITY_SHIFT 20
#define MAX_ARITY   (ARITY_MASK >> ARITY_SHIFT)

//
// Some compile-time checks
//
#if !(ETYPE_MASK + ARITY_N + ARITY_MASK + DTYPE_MASK + WIDTH_MASK == 0xFFFFFFFF)
#error "Some macros are overlapping ?"
#endif

#if !(ARITY_MASK >> ARITY_SHIFT == 0x07F)
#error "Wrong value for ARITY_SHIFT ?"
#endif

//
// Forward declaration
//
class Enode;
//
// Datatype for distinctions
//
typedef uint32_t dist_t;
//
// Data structure used to store forbid lists
//
struct Elist
{
  Elist *  link;            // Link to the next element in the list
  Enode *  e;               // Enode that differs from this
  Enode * reason;           // Reason for this distinction
};
//
// Data used for terms in congruence only
//
struct TermData
{
  TermData ( Enode * e )
    : value            ( NULL )
    , exp_reason       ( NULL )
    , exp_parent       ( NULL )
    , exp_root         ( e )
    , exp_class_size   ( 1 )
    , exp_highest_node ( e )
    , exp_time_stamp   ( 0 )
    , constant         ( NULL )
    , cb               ( e )
  { }

  Real *            value;            // The value
  Enode *           exp_reason;       // Reason for the merge of this and exp_parent
  Enode *           exp_parent;       // Parent in the explanation tree
  Enode *           exp_root;         // Compressed parent in the eq classes of the explanations
  int               exp_class_size;   // Size of the eq class of the explanation
  Enode *           exp_highest_node; // Highest node of the class
  int               exp_time_stamp;   // Time stamp for NCA
  Enode *           constant;         // Store the constant the node is currently equivalent with
  Enode *           cb;               // Pointer for coarsest base
};
//
// Data used for congruence closure, for
// both terms and lists
//
struct CongData
{
  CongData ( const enodeid_t id
           , Enode * e )
    : root         ( e )
    , cid          ( id )
    , next         ( e )
    , size         ( 1 )
    , parent       ( NULL )
    , same_car     ( NULL )
    , same_cdr     ( NULL )
    , parent_size  ( 0 )
    , cg_ptr       ( e )
    , forbid       ( NULL )
    , dist_classes ( 0 )
    , term_data    ( NULL )
  { }

  ~CongData ( )
  {
    if ( term_data ) delete term_data;
  }

  Enode *    root;           // Quick find
  enodeid_t  cid;            // Congruence id. It may change
  Enode *    next;           // Next element in equivalence class
  int        size;           // Size of the eq class of this node
  Enode *    parent;         // Parent in the congruence
  Enode *    same_car;       // Circular list of all the car-parents of the congruence
  Enode *    same_cdr;       // Circular list of all the cdr-parents of the congruence
  int        parent_size;    // Size of the parents of this eq class
  Enode *    cg_ptr;         // Congruence pointer. Parent node in the Fischer-Galler tree
  Elist *    forbid;         // List of enodes unmergable with this
  dist_t     dist_classes;   // Stores info about distictions
  TermData * term_data;      // Stores info about terms
};
//
// Data used for atom terms only
//
struct AtomData
{
  AtomData ( )
    : polarity     ( l_Undef )
    , deduced      ( l_Undef )
    , ded_index    ( -2 )
    , dist_index   ( -1 )
    , has_polarity ( false )
    , is_deduced   ( false )
    , dec_polarity ( l_Undef )
    , weight_inc   ( 0 )
  { }

  lbool   polarity;         // Associated polarity on the trail
  lbool   deduced;          // Associated deduced polarity. l_Undef means not deduced
  int     ded_index;        // Index of the solver that deduced this atom
  int     dist_index;       // If this node is a distinction, dist_index is the index in dist_classes that refers to this distinction
  bool    has_polarity;     // True if has polarity
  bool    is_deduced;       // True if deduced
  lbool   dec_polarity;     // Polarity to be used in decisions
  int     weight_inc;       // Initial weight increase
};
//
// Data for symbols and numbers
//
struct SymbData
{
  //
  // Constructor for Symbols
  //
  SymbData ( const char *         name_
           , const etype_t        etype_
	   , std::list<Sort*>&    arg_sort_
	   , Sort &               ret_sort_ )
      : name     ( NULL )
      , value    ( NULL )
      , lsb      ( -1 )
      , arg_sort ( arg_sort_ )
      , ret_sort ( ret_sort_ )
  {
    //
    // Variable
    //
    if ( etype_ == ETYPE_SYMB )
    {
      name = new char[ strlen( name_ ) + 1 ];
      strcpy( name, name_ );
    }
    //
    // Number
    //
    else if ( etype_ == ETYPE_NUMB )
    {
#if USE_GMP
      value = new Real( name_ );
      const int size_value = strlen( value->get_str( ).c_str( ) ) + 1;
      name = new char[ size_value ];
      strcpy( name, value->get_str( ).c_str( ) );
      assert( strlen( name ) == strlen( value->get_str( ).c_str( ) ) );
#else
      value = new Real;
      *value = atof( name_ );
      name = new char[ strlen(name_) + 1 ];
      strcpy( name, name_ );
#endif
    }
  }

  ~SymbData ( )
  {
    assert( name );
    delete [] name;
    if ( value )
      delete value;
  }

  char *             name;
  Real *             value;
  int                lsb;        // lsb for extraction, if -1 not extraction
  std::list<Sort*>&  arg_sort;
  Sort&              ret_sort;
};

#endif
