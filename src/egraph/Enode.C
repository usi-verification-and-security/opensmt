#include "Enode.h"

cgId Enode::cgid_ctr = cgId_Nil+1;
ERef Enode::ERef_Nil;



//
// Constructor for terms and lists
//

Enode::Enode(ERef car_,
             ERef cdr_,
             EnodeAllocator& ea,
             ERef er_,
             enodeid_t id_,
             PTRef ptr)
     : header({et_list, 0, id_}) // Fix the type to term later if necessary
     , er(er_)
     , cid(cgid_ctr++)

{
    assert(isTerm() || isList());
    setCar(car_);
    setCdr(cdr_);
    setRoot(er);
    setNext(er);
    setSize(1);
    setParent(ERef_Undef);
    setParentSize(0);

    Enode& x = ea[getCar()];
    Enode& y = ea[getCdr()];

    if (x.type() != et_symb) {
        // x is not a symbol
        if (x.getParent() == ERef_Undef) {
            x.setParent(er);
            setSameCar(er);
        }
        else {
            setSameCar(ea[x.getParent()].getSameCar());
            ea[x.getParent()].setSameCar(er);
        }
        x.setParentSize(x.getParentSize()+1);
    }
    else // x is a symbol
        setSameCar(er);

    if (y.type() != et_symb) {
        if (y.getParent() == ERef_Undef) {
            y.setParent(er);
            setSameCdr(er);
        }
        else {
            setSameCdr(ea[y.getParent()].getSameCdr());
            ea[y.getParent()].setSameCdr(er);
        }
        y.setParentSize(y.getParentSize()+1);
    }
    else {
        assert(getCdr() == ERef_Nil);
        setSameCdr(er);
    }
    setCgPtr(er);

    if (ptr != PTRef_Undef) {
        header.type = et_term;
        // Term specific data
        setDeduced(l_Undef);
        setDistClasses(0);
        setConstant(PTRef_Undef);
#ifdef CUSTOM_EL_ALLOC
        setForbid(ELRef_Undef);
#else
        setForbid(NULL);
#endif
        setPterm(ptr);
    }
}
