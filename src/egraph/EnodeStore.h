#ifndef ENODESTORE_H
#define ENODESTORE_H

#include "Enode.h"
#include "Term.h"
#include "Pterm.h"

class EnodeStore {
    Map<SigPair,ERef,SigHash,Equal<const SigPair&> > sig_tab;
    EnodeAllocator      ea;
    ERef                ERef_Nil;
  public:
    EnodeStore() :
        ea(1024*1024, &sig_tab)
      , ERef_Nil(ea.alloc(TRef_Undef))
        { Enode::ERef_Nil = ERef_Nil; } // Nil is a symbol.  Is this right?
    ERef addTerm(ERef sym, ERef args, PTRef pt);
    ERef addSymb(TRef t);
    ERef cons(ERef car, ERef cdr);
    ERef get_Nil() const { return ERef_Nil; }
    void free(ERef er) { ea.free(er); }
    vec<ERef>           id_to_enode;
    Enode& operator[] (ERef e) { return ea[e]; }
    Map<PTRef,ERef,PTRefHash,Equal<PTRef> > termToERef;
    Map<TRef,ERef, TRefHash,Equal<TRef> > symToERef;

    void removeParent(ERef, ERef);

//    inline const SigPair& getSig(ERef e) const
//        { const Enode& en_e = ea[e];
//          SigPair sp( ea[ea[en_e.getCar()].getRoot()].getCid(), ea[ea[en_e.getCdr()].getRoot()].getCid() );
//          return sp; }
    inline bool containsSig(ERef e) const
        { const Enode& en_e = ea[e];
          SigPair sp( ea[ea[en_e.getCar()].getRoot()].getCid(), ea[ea[en_e.getCdr()].getRoot()].getCid() );
          return sig_tab.contains(sp); }

    inline bool containsSig(ERef car, ERef cdr) const
        { SigPair sp( ea[ea[car].getRoot()].getCid(), ea[ea[cdr].getRoot()].getCid() );
          return sig_tab.contains(sp); }


    inline ERef lookupSig(ERef e) const
        { const Enode& en_e = ea[e];
          SigPair sp( ea[ea[en_e.getCar()].getRoot()].getCid(), ea[ea[en_e.getCdr()].getRoot()].getCid() );
          return sig_tab[sp]; }

    inline ERef lookupSig(ERef car, ERef cdr) const
        { SigPair sp( ea[ea[car].getRoot()].getCid(), ea[ea[cdr].getRoot()].getCid() );
          return sig_tab[sp]; }

    inline void removeSig(ERef e)
        { const Enode& en_e = ea[e];
          ERef carRoot = ea[en_e.getCar()].getRoot();
          ERef cdrRoot = ea[en_e.getCdr()].getRoot();
          SigPair sp( ea[carRoot].getCid(), ea[cdrRoot].getCid() );
          sig_tab.remove(sp);
          assert(!containsSig(e));
          }

    inline void insertSig(ERef e)
        { const Enode& en_e = ea[e];
          ERef carRoot = ea[en_e.getCar()].getRoot();
          ERef cdrRoot = ea[en_e.getCdr()].getRoot();
          assert(!containsSig(e));
          sig_tab.insert(SigPair(ea[carRoot].getCid(), ea[cdrRoot].getCid()), en_e.getCgPtr()); }
};

#endif
