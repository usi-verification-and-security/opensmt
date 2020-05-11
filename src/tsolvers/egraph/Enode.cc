/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen

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
     : header({et_list, id_}) // Fix the type to term later if necessary
     , er(er_)
     , cid(cgid_ctr++)

{
    assert(isTerm() || isList());
    setCar(car_);
    setCdr(cdr_);
    setRoot(er);
    setNext(er);
    setSize(1);
//    setParent(ERef_Undef);
//    setParentSize(0);
    setCarParentIndex(-1);
    setCdrParentIndex(-1);

//    Enode& x = ea[getCar()];
//    Enode& y = ea[getCdr()];

//    if (x.type() != et_symb) {
//        // x is not a symbol
//        if (x.getParent() == ERef_Undef) {
//            x.setParent(er);
//            setSameCar(er);
//        }
//        else {
//            setSameCar(ea[x.getParent()].getSameCar());
//            ea[x.getParent()].setSameCar(er);
//        }
//        x.setParentSize(x.getParentSize()+1);
//    }
//    else // x is a symbol
//        setSameCar(er);
//
//    if (y.type() != et_symb) {
//        if (y.getParent() == ERef_Undef) {
//            y.setParent(er);
//            setSameCdr(er);
//        }
//        else {
//            setSameCdr(ea[y.getParent()].getSameCdr());
//            ea[y.getParent()].setSameCdr(er);
//        }
//        y.setParentSize(y.getParentSize()+1);
//    }
//    else {
//        assert(getCdr() == ERef_Nil);
//        setSameCdr(er);
//    }
//    setCgPtr(er);

    if (ptr != PTRef_Undef) {
        header.type = et_term;
        // Term specific data
        setDistClasses(0);
        setForbid(ELRef_Undef);
        setPterm(ptr);
        setExpParent(ERef_Undef);
        setExpRoot(er);
        setExpReason(PtAsgn(PTRef_Undef, l_Undef));
        setExpTimeStamp(0);
    }
}
