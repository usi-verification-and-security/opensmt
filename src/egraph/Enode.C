#include "Enode.h"

cgId Enode::cgid_ctr = cgId_Nil+1;
ERef Enode::ERef_Nil;

//struct ELRef ELRef_Undef = { INT32_MAX };

Enode::Enode(ERef car_, ERef cdr_, en_type t, EnodeAllocator& ea, ERef er, PTRef pt, Map<SigPair,ERef,SigHash,Equal<const SigPair&> >& sig_tab) {

    header.type    = t;
    car            = car_;
    cdr            = cdr_;

    pterm          = pt;

    Enode& x = ea[car];
    Enode& y = ea[cdr];
    CgData& x_cgd = *x.cgdata;
    CgData& y_cgd = *y.cgdata;

    CgData& cgd   = *cgdata;

    cgd.root   = er;
    cgd.next   = er;
    cgd.size   = 1;
    cgd.parent = ERef_Nil;
    cgd.parent_size = 0;
    cgd.cid    = cgid_ctr++;

    if (x_cgd.parent == ERef_Nil) {
        x_cgd.parent  = er;
        cgd.same_car  = er;
    }
    else {
        cgd.same_car = ea[x_cgd.parent].cgdata->same_car;
        ea[x_cgd.parent].cgdata->same_car = er;
    }
    ea[x_cgd.parent].cgdata->parent_size++;

    if (y_cgd.parent == ERef_Nil) {
        y_cgd.parent = er;
        cgd.same_cdr = er;
    }
    ea[y_cgd.parent].cgdata->parent_size++;

    cgd.cg_ptr = er;
    SigPair p(x.cgdata->cid,y.cgdata->cid);
    sig_tab.insert(p, er);
}




