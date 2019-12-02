/*********************************************************************
Author: Antti Hyvarinen <antti.hyvarinen@gmail.com>

OpenSMT2 -- Copyright (C) 2012 - 2014 Antti Hyvarinen
                          2008 - 2012 Roberto Bruttomesso

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

#include "SStore.h"



SRef SStore::newSort(IdRef id, const char* name_, vec<SRef>& rest)
{
    if (sortTable.has(name_))
        return sortTable[name_];
    else {
        char* name = strdup(name_);
        SStrRef nr = ssa.alloc(name);
        SRef sr = sa.alloc(id, nr, rest);
        sorts.push(sr);
        sortTable.insert(name, sr);
        sort_names.push(name);
        return sr;
    }
}
SRef SStore::newSort(IdRef idr, vec<SRef>& rest)
{
    SRef sr = SRef_Undef;
    std::string canon_name;
    if (rest.size() > 0) {
        std::stringstream ss;
        ss << is.getName(idr);
        ss << " (";
        ss << getName(rest[0]);
        for (int i = 1; i < rest.size(); i++) {
            ss << ' ';
            ss << getName(rest[i]);
        }
        ss << ')';
        canon_name = ss.str();
    } else {
        canon_name = is.getName(idr);
    }

    const char* c_canon_name = canon_name.c_str();
    if (sortTable.has(c_canon_name)) {
        SRef sr = sortTable[c_canon_name];
        return sr;
    } else {
        char* new_name = strdup(c_canon_name);
        SStrRef nr = ssa.alloc(new_name);
        sr = sa.alloc(idr, nr, rest);
        sorts.push(sr);
        sortTable.insert(new_name, sr);
        sort_names.push(new_name);
        return sr;
    }
}

void
SStore::dumpSortsToFile ( ostream & dump_out )
{
    for(int i = 1; i < sorts.size(); ++i)
	{
		dump_out << "(declare-sort " << getName(sorts[i]) << " 0)" << endl;
	}
}
