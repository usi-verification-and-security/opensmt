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

#include <string>
#include <sstream>

SRef SStore::newSort(Identifier idr, vec<SRef> const & rest)
{
    SRef sr = SRef_Undef;
    std::string canon_name;
    if (rest.size() > 0) {
        std::stringstream ss;
        ss << idr.name;
        ss << " (";
        ss << getName(rest[0]);
        for (int i = 1; i < rest.size(); i++) {
            ss << ' ';
            ss << getName(rest[i]);
        }
        ss << ')';
        canon_name = ss.str();
    } else {
        canon_name = idr.name;
    }

    const char* c_canon_name = canon_name.c_str();
    if (sortTable.has(c_canon_name)) {
        return sortTable[c_canon_name];
    } else {
        char* new_name = strdup(c_canon_name);
        sr = sa.alloc(std::move(idr), rest);
        sorts.push(sr);
        sortTable.insert(new_name, sr);
        sort_names.push(new_name);
        return sr;
    }
}

void
SStore::dumpSortsToFile ( std::ostream & dump_out )
{
    for(int i = 1; i < sorts.size(); ++i)
	{
		dump_out << "(declare-sort " << getName(sorts[i]) << " 0)" << std::endl;
	}
}
