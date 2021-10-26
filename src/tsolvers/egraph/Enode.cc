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
UseVectorIndex UseVectorIndex::NoIndex = {-1};
UseVectorIndex UseVectorIndex::DuplicateIndex = {-2};

Enode::Enode(EnodeAllocator& ea, SymRef symbol, ERefSpan children, ERef myRef, PTRef term)
     : cid(cgid_ctr++), pterm(term), symb(symbol), argSize(children.getSize())
{
    setRoot(myRef);
    setEqNext(myRef);
    setEqSize(1);

    assert(term != PTRef_Undef);
    // Term specific data
    setDistClasses(0);
    setForbid(ELRef_Undef);
    setExpParent(ERef_Undef);
    setExpRoot(myRef);
    setExpReason(PtAsgn(PTRef_Undef, l_Undef));
    setExpTimeStamp(0);
    for (uint32_t i = 0; i < children.getSize(); ++i) {
        args[i] = children[i];
        setIndex(i, UseVectorIndex::NoIndex);
    }
}
