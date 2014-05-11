#include "Enode.h"

cgId Enode::cgid_ctr = cgId_Nil+1;
ERef Enode::ERef_Nil;

//struct ELRef ELRef_Undef = { INT32_MAX };

Enode::Enode(SymRef tr_, ERef er_) : symb(tr_), er(er_) {
    header.type = et_symb;
    cid = cgid_ctr++;
    deduced = l_Undef;
    has_polarity = false;
}

Enode::Enode(ERef car_, ERef cdr_,
             en_type t, EnodeAllocator& ea,
             ERef er_, Map<SigPair,ERef,SigHash,Equal<const SigPair&> >& sig_tab)
     : er(er_)
{
    deduced = l_Undef;
    has_polarity = false;

    header.type    = t;
    car            = car_;
    cdr            = cdr_;

    cgdata->dist_classes = 0;

    Enode& x = ea[car];
    Enode& y = ea[cdr];

    // What if x is symbol
    // What if y is nil
    CgData& x_cgd = *x.cgdata;
    CgData& y_cgd = *y.cgdata;

    CgData& cgd   = *cgdata;

    cgd.root   = er;
    cgd.next   = er;
    cgd.size   = 1;
    cgd.parent = ERef_Undef;
    cgd.parent_size = 0;
    cid    = cgid_ctr++;

    if (x.type() != et_symb) {
        // x is not a symbol
        if (x_cgd.parent == ERef_Undef) {
            x_cgd.parent  = er;
            cgd.same_car  = er;
        }
        else {
            cgd.same_car = ea[x_cgd.parent].cgdata->same_car;
            ea[x_cgd.parent].cgdata->same_car = er;
        }
        x_cgd.parent_size++;
    }
    else // x is a symbol
        cgd.same_car = er;

    if (y.type() != et_symb) {
        if (y_cgd.parent == ERef_Undef) {
            y_cgd.parent = er;
            cgd.same_cdr = er;
        }
        else {
            cgd.same_cdr = ea[y_cgd.parent].cgdata->same_cdr;
            ea[y_cgd.parent].cgdata->same_cdr = er;
        }
        y_cgd.parent_size++;
    }
    else {
        assert(cdr == ERef_Nil);
        cgd.same_cdr = er;
    }
    cgd.cg_ptr = er;

    cgd.forbid = ELRef_Undef;
}




