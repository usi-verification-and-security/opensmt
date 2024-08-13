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

namespace opensmt {

cgId Enode::cgid_ctr = cgId_Nil+1;
UseVectorIndex UseVectorIndex::NotValidIndex = {UINT32_MAX};

Enode::Enode(SymRef symbol, span<ERef> children, ERef myRef, PTRef term) :
    root(myRef),
    cid(cgid_ctr++),
    eq_next(myRef),
    eq_size(1),
    pterm(term),
    forbid(ELRef_Undef),
    dist_classes(0),
    exp_reason(PTRef_Undef, l_Undef),
    exp_parent(ERef_Undef),
    exp_root(myRef),
    exp_time_stamp(0),
    symb(symbol),
    argSize(children.size())
{
    assert(term != PTRef_Undef);
    for (uint32_t i = 0; i < argSize; ++i) {
        args[i] = children[i];
        setIndex(i, UseVectorIndex::NotValidIndex);
    }
}

}
