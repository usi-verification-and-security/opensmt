/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT -- Copyright (C) 2010, Roberto Bruttomesso

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

#ifndef ENODE_H
#define ENODE_H

#include "Vec.h"
#include "Alloc.h"

#include "terms/Term.h"

//#include "Global.h"
//#include "EnodeTypes.h"
//#include "Otl.h"
#include "sorts/Sort.h"
#include "CgTypes.h"
#include "SigMap.h"

typedef RegionAllocator<uint32_t>::Ref ERef;

class CgData {
    ERef        root;           // Root of the equivalence class
    cgId        cid;            // The "congruence id" of the class
    ERef        next;           // Next node in the class
    int         size;           // Size of the eq class
    ERef        parent;         // Parent of the node (in congruence)
    ERef        same_car;       // Circular list of all the car-parents of the class
    ERef        same_cdr;       // Circular list of all the cdr-parents of the class
    int         parent_size;    // Size of the parent's congruence class
    ERef        cg_ptr;         // Congruence class representative (how is this different from root?)
    vec<ERef>*  forbid;         // List of unmergeable Enodes
    dist_t      dist_classes;   // The bit vector for distinction classes

    friend class Enode;
};

class EnodeAllocator;

static ERef const ERef_Undef = RegionAllocator<uint32_t>::Ref_Undef;

class Enode
{
    static uint32_t cgid_ctr;

    struct {
        unsigned type       : 2;
        unsigned reloced    : 1;
        unsigned unused     : 29; } header;

    TRef        tr;
    uint32_t    id;
    ERef        er;     // Either my tref or reference to the relocated one
    ERef        car;
    ERef        cdr;

    // This is a trick to enable congruence data on only Enodes it is needed
    CgData      cgdata[0];


    friend class EnodeAllocator;
    friend class EnodeStore;

public:
    static ERef ERef_Nil;

    enum en_type { et_symb, et_list, et_term };

    // Constructor for symbol and singleton term nodes
    Enode(TRef tr_) : tr(tr_) { header.type = et_symb; }

    // Constructor for the non-singleton term and list nodes
    Enode(ERef car_, ERef cdr_, en_type t, EnodeAllocator& ea, ERef er, Map<SigPair,ERef,SigHash,Equal<const SigPair&> >& sig_tab);

    Enode* Enode_new(en_type t, TRef tr) {
        assert(sizeof(TRef) == sizeof(uint32_t));
        size_t sz = sizeof(header) + sizeof(TRef) + sizeof(uint32_t);
        if (t != et_symb) sz += sizeof(CgData);
        void* mem = malloc(sz);

        if (t == et_term) {
            Enode* en = new (mem) Enode(tr);
            new (en->cgdata) CgData();
        }
        return new (mem) Enode(tr);

    }

    en_type type        ()        const { return (en_type)header.type; }

    void relocate       (ERef e)        { header.reloced = 1; er = e; }
    bool reloced        ()        const { return header.reloced; }
    ERef relocation     ()        const { return er; }

    friend class CgData;
};

class EnodeAllocator : public RegionAllocator<uint32_t>
{
    static int enodeWord32Size(bool has_cgdata){
        if (has_cgdata) return (sizeof(Enode) + sizeof(CgData))/sizeof(int32_t);
        else            return sizeof(Enode)/sizeof(int32_t); }

    Map<SigPair,ERef,SigHash,Equal<const SigPair&> >* sig_tab;

 public:

    EnodeAllocator(uint32_t start_cap, Map<SigPair,ERef,SigHash,Equal<const SigPair&> >* st) : RegionAllocator<uint32_t>(start_cap), sig_tab(st) {}
    EnodeAllocator() {}

    void moveTo(EnodeAllocator& to){
        RegionAllocator<uint32_t>::moveTo(to); }

    ERef alloc(TRef tr) {
        assert(sizeof(TRef)     == sizeof(uint32_t));
        assert(sizeof(ERef)     == sizeof(uint32_t));
        ERef eid = RegionAllocator<uint32_t>::alloc(enodeWord32Size(false));
        new (lea(eid)) Enode(tr);

        return eid;
    }

    ERef alloc(ERef car, ERef cdr, Enode::en_type t)
    {
        assert(sizeof(TRef)     == sizeof(uint32_t));
        assert(sizeof(ERef)     == sizeof(uint32_t));

        bool has_cgdata = (t == Enode::et_list) || (t == Enode::et_term);
        ERef eid = RegionAllocator<uint32_t>::alloc(enodeWord32Size(has_cgdata));
        new (lea(eid)) Enode(car, cdr, t, *this, eid, *sig_tab);

        return eid;
    }

    ERef alloc(Enode&) {
        assert(false);
        return ERef_Undef;
    }

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Enode&       operator[](Ref r)         { return (Enode&)RegionAllocator<uint32_t>::operator[](r); }
    const Enode& operator[](Ref r) const   { return (Enode&)RegionAllocator<uint32_t>::operator[](r); }
    Enode*       lea       (Ref r)         { return (Enode*)RegionAllocator<uint32_t>::lea(r); }
    const Enode* lea       (Ref r) const   { return (Enode*)RegionAllocator<uint32_t>::lea(r); }
    Ref          ael       (const Enode* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(ERef eid)
    {
        Enode& e = operator[](eid);
        if ((e.type() == Enode::et_list) || (e.type() == Enode::et_term))
            RegionAllocator<uint32_t>::free(enodeWord32Size(true));
        else
            RegionAllocator<uint32_t>::free(enodeWord32Size(false));

    }

    void reloc(ERef& er, EnodeAllocator& to)
    {
        Enode& e = operator[](er);

        if (e.reloced()) { er = e.relocation(); return; }

        er = to.alloc(e);
        e.relocate(er);
    }
};




/*
  Enode ( const enodeid_t, TRef ) :
      id(geid++);
    , header.type(ETYPE_SYM)
  //
  // Constructor for terms and lists
  //
  Enode ( const enodeid_t       // id
        , Enode *               // car
        , Enode *               // cdr
        );
  //
  // Constructor for defs -- what is a def?
  //
  Enode ( const enodeid_t       // id
        , Enode *               // def
        );
  //
  // Destructor
  //
  ~Enode ( );
  //
  // Check if a node is Enil
  //
  inline bool isEnil            ( ) const { return id == ENODE_ID_ENIL; }
  inline bool isList            ( ) const { return (properties & ETYPE_MASK) == ETYPE_LIST; }
  inline bool isTerm            ( ) const { return (properties & ETYPE_MASK) == ETYPE_TERM; }
  inline bool isSymb            ( ) const { return (properties & ETYPE_MASK) == ETYPE_SYMB; }
  inline bool isNumb            ( ) const { return (properties & ETYPE_MASK) == ETYPE_NUMB; }
  inline bool isDef             ( ) const { return (properties & ETYPE_MASK) == ETYPE_DEF; }

  inline void setEtype          ( const etype_t t )
  {
    assert( t == ETYPE_SYMB
         || t == ETYPE_NUMB
         || t == ETYPE_LIST
         || t == ETYPE_TERM
         || t == ETYPE_DEF );
    properties |= t;
  }

  inline void setArity            ( const unsigned a ) { assert( a <= ARITY_N ); properties |= (a << ARITY_SHIFT); }

  inline bool hasCongData         ( ) const { return cong_data != NULL; }
  void        allocCongData       ( );
  void        deallocCongData     ( );

  //
  // Getty and Setty methods
  //
  inline enodeid_t            getId      ( ) const { return id; }
  inline TRef                 getTerm    ( ) const { return tr; }

  inline Enode *  getCar                 ( ) const { return car; }
  inline Enode *  getCdr                 ( ) const { return cdr; }
//  inline Enode *  getDef                 ( ) const { assert( isDef( ) ); assert( car ); return car; }

  inline Enode *  getNext                ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->next; }
  inline int      getSize                ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->size; }
  inline Enode *  getParent              ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->parent; }
  inline Enode *  getSameCar             ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->same_car; }
  inline Enode *  getSameCdr             ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->same_cdr; }
  inline int      getParentSize          ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->parent_size; }
  inline Enode *  getCgPtr               ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->cg_ptr; }
  inline Elist *  getForbid              ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->forbid; }
  inline dist_t   getDistClasses         ( ) const { assert( isTerm( ) || isList( ) ); assert( cong_data ); return cong_data->dist_classes; }

  Enode *         getRoot                ( ) const;
  enodeid_t       getCid                 ( ) const;
  Enode *         getConstant            ( ) const;
                  
  inline Enode *  getExpReason           ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_reason; }
  inline Enode *  getExpParent           ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_parent; }
  inline Enode *  getExpRoot             ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_root; }
  inline int      getExpClassSize        ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_class_size; }
  inline Enode *  getExpHighestNode      ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_highest_node; }
  // inline Reason * getExpReason           ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_reason; }
  inline int      getExpTimeStamp        ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->exp_time_stamp; }

  inline lbool    getPolarity            ( ) const { assert( isTerm( ) && atom_data ); return atom_data->polarity; }
  inline bool	  hasPolarity            ( ) const { assert( isTerm( ) && atom_data ); return atom_data->has_polarity; }
  inline lbool    getDeduced             ( ) const { assert( isTerm( ) && atom_data ); return atom_data->deduced; }
  inline bool     isDeduced              ( ) const { assert( isTerm( ) && atom_data ); return atom_data->is_deduced; }
  inline lbool    getDecPolarity         ( )       { assert( isAtom( ) && atom_data ); return atom_data->dec_polarity; }
  inline int      getWeightInc           ( )       { assert( isAtom( ) && atom_data ); return atom_data->weight_inc; }
  inline int      getDedIndex            ( ) const { assert( isTerm( ) && atom_data ); return atom_data->ded_index; }
  inline int      getDistIndex           ( ) const { assert( isTerm( ) && atom_data ); return atom_data->dist_index; }

  inline Enode *  getCb                  ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->term_data->cb; }
  inline Enode *  getRef                 ( ) const { assert( isTerm( ) && cong_data && cong_data->term_data ); return cong_data->root; }
  inline int      getWidth               ( ) const { assert( isTerm( ) || isSymb( ) || isNumb( ) ); return (properties & WIDTH_MASK); }

  inline void     setWidth               ( const uint32_t w )
  {
    assert( isTerm( ) );
    assert( w < MAX_WIDTH );
    // Reset width
    properties &= ~WIDTH_MASK;
    properties |= w;
    assert( getWidth( ) == static_cast<int>( w ) );
  }

  inline void    setRoot                ( Enode * e )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->root = e; }
  inline void    setCid                 ( const enodeid_t c ){ assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->cid = c; } // Congruence id?
  inline void    setDef                 ( Enode * e )        { assert( e ); assert( isDef( ) ); car = e; }
  inline void    setNext                ( Enode * e )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->next = e; }
  inline void    setSize                ( const int s )      { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->size = s; }
  inline void    setParent              ( Enode * e )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->parent = e; }
  inline void    setSameCar             ( Enode * e )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->same_car = e; }
  inline void    setSameCdr             ( Enode * e )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->same_cdr = e; }
  inline void    setParentSize          ( const int s )      { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->parent_size = s; }
  inline void    setCgPtr               ( Enode * e )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->cg_ptr = e; }
  inline void    setForbid              ( Elist * l )        { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->forbid = l; }
  inline void    setDistClasses         ( const dist_t & d ) { assert( isTerm( ) || isList( ) ); assert( cong_data ); cong_data->dist_classes = d; }

  inline void    setConstant            ( Enode * e )            { assert( isTerm( ) && cong_data && cong_data->term_data ); assert( e == NULL || e->isConstant( ) ); cong_data->term_data->constant = e; }
  inline void    setExpReason           ( Enode * r )            { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->exp_reason = r; }
  inline void    setExpParent           ( Enode * e )            { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->exp_parent = e; }
  inline void    setExpRoot             ( Enode * e )            { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->exp_root = e; }
  inline void    setExpClassSize        ( const int s )          { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->exp_class_size = s; }
  inline void    setExpHighestNode      ( Enode * e )            { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->exp_highest_node = e; }
  inline void    setExpTimeStamp        ( const int t )          { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->exp_time_stamp = t; }
  inline void    setPolarity            ( const lbool p )        { assert( isTerm( ) && atom_data ); assert( !atom_data->has_polarity ); atom_data->polarity = p; atom_data->has_polarity = true; }
  inline void    resetPolarity          ( )			 { assert( isTerm( ) && atom_data ); assert( atom_data->has_polarity ); atom_data->has_polarity = false; }
  inline void    setDeduced             ( const lbool d, int i ) { assert( isTerm( ) && atom_data ); assert( !atom_data->is_deduced ); atom_data->deduced = d; atom_data->ded_index = i; atom_data->is_deduced = true; }
  inline void    setDeduced             ( const bool s, int i )  { setDeduced( s ? l_False : l_True, i ); }
  inline void    resetDeduced           ( )			 { assert( isTerm( ) && atom_data ); assert( atom_data->is_deduced ); atom_data->is_deduced = false; }
  inline void    setDecPolarity         ( const lbool s )        { assert( isAtom( ) && atom_data ); atom_data->dec_polarity = s; }
  inline void    setWeightInc           ( const int w )          { assert( isAtom( ) && atom_data ); atom_data->weight_inc = w; }
  inline void    setDistIndex           ( const int d )	         { assert( isTerm( ) && atom_data ); atom_data->dist_index = d; }

  inline void    setCb                  ( Enode * e )            { assert( isTerm( ) && cong_data && cong_data->term_data ); cong_data->term_data->cb = e; }

  //
  // Congruence closure related routines
  //
  void           addParent              ( Enode * );   // Adds a parent to this node. Useful for congruence closure
  void           addParentTail          ( Enode * );   // Adds a parent to the tail of this node. Useful for congruence closure
  void           removeParent           ( Enode * );   // Remove a parent of this node
  //
  // Shortcuts for retrieving a term's arguments
  //
  inline Enode * get1st                 ( ) const;     // Get first argument in constant time (constant?)
  inline Enode * get2nd                 ( ) const;     // Get second argument in constant time
  inline Enode * get3rd                 ( ) const;     // Get third argument in constant time

  bool           addToCongruence        ( ) const;
  unsigned       sizeInMem              ( ) const;

  void           print                  ( ostream & ); // Prints the enode
  string         stripName              ( string );
  void           printSig               ( ostream & ); // Prints the enode signature

#ifdef BUILD_64
  inline enodeid_pair_t          getSig    ( ) const { return encode( car->getRoot( )->getCid( ), cdr->getRoot( )->getCid( ) ); }
#else
  inline const Pair( enodeid_t ) getSig    ( ) const { return make_pair( car->getRoot( )->getCid( ), cdr->getRoot( )->getCid( ) ); }
#endif
  inline enodeid_t               getSigCar ( ) const { return car->getRoot( )->getCid( ); }
  inline enodeid_t               getSigCdr ( ) const { return cdr->getRoot( )->getCid( ); }

#ifdef PRODUCE_PROOF
  inline const ipartitions_t & getIPartitions ( ) const                   { return ipartitions; }
  inline void                  setIPartitions ( const ipartitions_t & p ) { assert( ipartitions == 0 ); ipartitions = p; }
  inline void                  addIPartitions ( const ipartitions_t & p ) { assert( p != 0 ); ipartitions |= p; }
  // inline void                  oveIPartitions ( const ipartitions_t & p ) { assert( p != 0 ); ipartitions = p; }
#endif

  inline friend ostream & operator<<( ostream & os, Enode * e )    { assert( e ); e->print( os ); return os; }

  struct idLessThan
  {
    inline bool operator( )( Enode * x, Enode * y ) const
    {
      const Enode *x_car = x->getCar();
      const Enode *y_car = y->getCar();
      const enodeid_t x_car_id = x_car->getId();
      const enodeid_t y_car_id = y_car->getId();

      return (x_car_id < y_car_id)
	  || (x_car_id == y_car_id && x->getCdr( )->getId( ) < y->getCdr( )->getId( ) );
    }
  };

  struct cidLessThan
  {
    inline bool operator( )( Enode * x, Enode * y ) const
    {
      if ( x == y ) return false;
      if ( x->isEnil( ) ) return true;
      if ( y->isEnil( ) ) return false;
      return (x->getCar( )->getCid( ) <  y->getCar( )->getCid( ))
          || (x->getCar( )->getCid( ) == y->getCar( )->getCid( ) && x->getCdr( )->getCid( ) < y->getCdr( )->getCid( ) );
    }
  };

private:
  //
  // Standard informations for terms
  //
  const enodeid_t   id;          // Node unique identifier
  uint32_t          properties;  // Contains all the properties of this node (see EnodeTypes.h for bitfields definition)
  Enode *           car;         // For car / defs
  Enode *           cdr;         // For cdr
  union {
  CongData *        cong_data;   // For terms and lists that go in the congruence
  SymbData *        symb_data;   // For symbols/numbers
  };
  AtomData *        atom_data;   // For atom terms only
#ifdef PRODUCE_PROOF
  ipartitions_t     ipartitions; // Partitions for interpolation
#endif

  inline bool       hasSymbolId    ( const enodeid_t id ) const { assert( isTerm( ) ); return car->getId( ) == id; }
};


inline Enode * Enode::getRoot ( ) const
{
  assert( !isDef( ) );
  if ( (isTerm( ) || isList( )) && cong_data != NULL )
    return cong_data->root;
  return const_cast<Enode *>(this);
}

inline enodeid_t Enode::getCid ( ) const
{
  assert( !isDef( ) );
  if ( (isTerm( ) || isList( )) && cong_data )
    return cong_data->cid;
  return id;
}


inline Enode * Enode::get1st ( ) const
{
  assert( isTerm( ) );
  assert( getArity( ) > 0 );
  return getCdr( )->getCar( );
}

inline Enode * Enode::get2nd ( ) const
{
  assert( isTerm( ) );
  assert( getArity( ) > 1 );
  return getCdr( )->getCdr( )->getCar( );
}

inline Enode * Enode::get3rd ( ) const
{
  assert( isTerm( ) );
  assert( getArity( ) > 2 );
  return getCdr( )->getCdr( )->getCdr( )->getCar( );
}

inline unsigned Enode::sizeInMem( ) const
{
  assert(value == NULL);
  unsigned size = sizeof( Enode );
  if ( isSymb( ) )
  {
    assert( symb_data );
    assert( symb_data->name );
    size += sizeof( SymbData ) + strlen( symb_data->name );
  }
  if ( isNumb( ) )
  {
    assert( symb_data );
    assert( symb_data->name );
    assert( symb_data->value );
    size += sizeof( SymbData ) + strlen( symb_data->name ) + sizeof( Real );
  }
  if ( atom_data ) size += sizeof( AtomData );
  if ( cong_data )
  {
    size += sizeof( CongData );
    if ( cong_data->term_data ) size += sizeof( TermData );
  }
#ifdef PRODUCE_PROOF
  size += ipartitions.get_mpz_t()->_mp_alloc * sizeof(ipartitions.get_mpz_t()->_mp_d[0]);
#endif
  return size;
}

inline void Enode::allocCongData( )
{
  assert( isTerm( ) || isList( ) );
  assert( cong_data == NULL );
  cong_data = new CongData( id, const_cast<Enode *>(this) );
  if ( isTerm( ) )
    cong_data->term_data = new TermData( const_cast<Enode *>(this) );
}

inline void Enode::deallocCongData( )
{
  assert( isTerm( ) || isList( ) );
  assert( cong_data != NULL );
  if ( isTerm( ) )
  {
    assert( cong_data->term_data != NULL );
    delete cong_data->term_data;
    cong_data->term_data = NULL;
  }
  delete cong_data;
  cong_data = NULL;
}
*/
#endif
