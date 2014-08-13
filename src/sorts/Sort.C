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


#include "Sort.h"

//const SRef SRef_Undef = -1;

//=============================================================================
// Sort constructor
//

//Sort::Sort(ASTNode& sn)
//{
//    uniq_id = static_uniq_id++;
//    stringstream ss;
//    if (sn.getType() == CMD_T) {
//        list<ASTNode*>::iterator p = sn.children->begin();
//        ASTNode& sym_name = **p; p++;
//        ASTNode& num      = **p;
//        id = new Identifier(sym_name);
//        par_num = atoi(num.getValue());
//        stype = SORT_ID_SIMPL;
//        ss << sym_name.getValue();
//        ss << " " << par_num;
//        canon_name = strdup(ss.str().c_str());
//    }
//    else if (sn.getType() == ID_T) {
//        id = new Identifier(**(sn.children->begin()));
//        stype = SORT_ID_SIMPL;
//        ss << id->toString();
//        ss << " " << 0;
//        canon_name = strdup(ss.str().c_str());
//    }
//    else if (sn.getType() == LID_T) {
//        // this is certainly broken
//        type = S_ID_LIST;
//        list<ASTNode*>::iterator it = sn.children->begin();
//        id = new Identifier(**(it++));
//        for (; it != sn.children->end(); it++)
//            rest_sorts.push(new Sort(**it));
//        // Check this from the logic?
//        stype = SORT_ID_CMPLX;
//        canon_name = strdup(ss.str().c_str());
//    }
//    else assert(false);
//}

//Sort::Sort(Identifier& id, vec<Sort*>& rest) : id(&id)
//{
//    uniq_id = static_uniq_id++;
//    if (rest.size() == 0)
//        stype = SORT_ID_SIMPL;
//    else {
//        for (int i = 0; i < rest.size(); i++)
//            rest_sorts.push(rest[i]);
//        stype = SORT_ID_CMPLX;
//    }
//    stringstream ss;
//    ss << id.toString();
//    if (type != S_ID) {
//        ss << " ( ";
//        for (int i = 0; i < rest_sorts.size(); i++)
//            ss << (*(rest_sorts[i])).getCanonName() << " ";
//        ss << ") ";
//    }
//    canon_name = strdup(ss.str().c_str());
//};
//
//Sort::Sort(Identifier& id) : id(&id)
//{
//    stringstream ss;
//    ss << id.toString();
//    if (id.getType() == IDTYPE_SIMPLE) ss << " 0";
//    canon_name = strdup(ss.str().c_str());
//    uniq_id = static_uniq_id++;
//};

sortid_t SortAllocator::static_uniq_id = 0;


