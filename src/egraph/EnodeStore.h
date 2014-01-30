#ifndef ENODESTORE_H
#define ENODESTORE_H

#include "Enode.h"
#include "Symbol.h"
#include "PtStore.h"

class EnodeStore {
    SymStore&      sym_store;
    PtStore&       term_store;
    Map<SigPair,ERef,SigHash,Equal<const SigPair&> > sig_tab;
    EnodeAllocator ea;
    ERef           ERef_Nil;
    ERef           ERef_True;
    ERef           ERef_False;
    Map<PTRef,char,PTRefHash,Equal<PTRef> > dist_classes;
    uint32_t       dist_idx;

#ifdef PEDANTIC_DEBUG
    ELAllocator&   fa;
#endif

    vec<PTRef>     index_to_dist;                    // Table distinction index --> proper term

    vec<ERef>      enodes;

  public:
#ifdef PEDANTIC_DEBUG
    EnodeStore(SymStore& syms, PtStore& terms, ELAllocator& fa_) :
        sym_store(syms)
      , term_store(terms)
      , ea(1024*1024, &sig_tab)
      , ERef_Nil(ea.alloc(SymRef_Undef))
      , dist_idx(0)
      , fa(fa_)
#else
    EnodeStore(SymStore& syms, PtStore& terms) :
        sym_store(syms)
      , term_store(terms)
      , ea(1024*1024, &sig_tab)
      , ERef_Nil(ea.alloc(SymRef_Undef))
      , dist_idx(0)
#endif
        { Enode::ERef_Nil = ERef_Nil; } // Nil is a symbol.  It should
                                        // in theory be list, but makes no matter now


    ERef getEnode_true()  { return ERef_True;  }
    ERef getEnode_false() { return ERef_False; }

    PTRef addTerm(ERef sym, ERef args, PTRef pt);
    ERef  addSymb(SymRef t);
    ERef  addList(ERef car, ERef cdr);

    void undoTerm(ERef);
    void undoList(ERef);

    ERef get_Nil() const { return ERef_Nil; }
    void free(ERef er) { ea.free(er); }
    vec<ERef>           id_to_enode;
    Enode& operator[] (ERef e) { return ea[e]; }
    const Enode& operator[] (ERef e) const { return ea[e]; }
    Map<PTRef,ERef,PTRefHash,Equal<PTRef> >     termToERef;
    Map<SymRef,ERef,SymRefHash,Equal<SymRef> > symToERef;
    Map<ERef,PTRef,ERefHash,Equal<ERef> >       ERefToTerm;

    void removeParent(ERef, ERef);
    char* printEnode(ERef);

    char getDistIndex(PTRef tr_d) const {
        assert(dist_classes.contains(tr_d));
        return dist_classes[tr_d];
    }

    PTRef getDistTerm(dist_t idx) { return index_to_dist[idx]; }

    void addDistClass(PTRef tr_d) {
        assert(!dist_classes.contains(tr_d));
        assert(dist_idx < sizeof(dist_t)*8);
        dist_classes.insert(tr_d, dist_idx);
        assert(index_to_dist.size_() == dist_idx);
        index_to_dist.push(tr_d);
        dist_idx++;
    }

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
          sig_tab.insert(SigPair(ea[carRoot].getCid(), ea[cdrRoot].getCid()), en_e.getCgPtr());
#ifdef PEDANTIC_DEBUG
//          SigPair(ea[carRoot.getCid(), ea[cdrRoot].getCid()])
#endif
        }
// DEBUG
#ifdef PEDANTIC_DEBUG
    bool checkInvariants();
#endif
    friend class Egraph;
};

#endif
