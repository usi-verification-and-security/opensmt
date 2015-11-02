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



SRef SStore::newSort(IdRef id, const char* name, vec<SRef>& rest)
{
    if (sortTable.contains(name))
        return sortTable[name];
    else {
        SStrRef nr = ssa.alloc(name);
        SRef sr = sa.alloc(id, nr, rest);
        sorts.push(sr);
        sortTable.insert(name, sr);
        return sr;
    }
}
SRef SStore::newSort(IdRef idr, vec<SRef>& rest)
{
    SRef sr = SRef_Undef;
    char* canon_name = NULL;
    char* old;
    if (rest.size() > 0) {
        char* arg_names;
        asprintf(&arg_names, "%s", getName(rest[0]));
        for (int i = 1; i < rest.size(); i++) {
            old = arg_names;
            asprintf(&arg_names, "%s %s", old, getName(rest[i]));
            free(old);
        }
        old = canon_name;
        asprintf(&canon_name, "%s (%s)", is.getName(idr), old);
        free(old);
    } else
        asprintf(&canon_name, "%s", is.getName(idr));

    if (sortTable.contains(canon_name)) {
        SRef sr = sortTable[canon_name];
        free(canon_name);
        return sr;
    } else {
        SStrRef nr = ssa.alloc(canon_name);
        sr = sa.alloc(idr, nr, rest);
        sorts.push(sr);
        sortTable.insert(canon_name, sr);
        return sr;
    }
}


//void SStore::insertStore(Sort* s) {
//    // temporary hack, finally a finer mem allocation for Sort would be nice?
//    assert(sorts.size() == SRefToSort.size());
//    const char* name = s->getCanonName();
//    SRef sr = sorts.size();
//    sorts.push(sr);
//    sortTable.insert(name, sr);
//    SRefToSort.push(s);
//}

int* IdentifierStore::serializeIdentifiers() const
{
    int* idstr_buf = isa.serialize();
    int* id_buf = ia.serialize();
    int id_strbuf_sz = idstr_buf[0];
    int id_buf_sz = id_buf[0];
    int buf_sz = id_strbuf_sz + id_buf_sz + 3;
    int* buf = (int*)malloc(buf_sz*sizeof(int));

    int str_offs = 3;
    int id_offs = str_offs + id_strbuf_sz;

    buf[0] = buf_sz;
    buf[1] = str_offs;
    buf[2] = id_offs;

    for (int i = 0; i < idstr_buf[0]; i++)
        buf[str_offs+i] = idstr_buf[i];

    for (int i = 0; i < id_buf[0]; i++)
        buf[id_offs+i] = id_buf[i];

    return buf;
}

void IdentifierStore::deserializeIdentifiers(const int* buf)
{
    int buf_sz = buf[0];
    int str_offs = buf[1];
    int id_offs = buf[2];

    isa.deserialize(&buf[str_offs]);
    ia.deserialize(&buf[id_offs]);
}


//
// Serialize the sorts
//
int* SStore::serializeSorts() const
{
    int* buf = NULL;
    int* idstore_buf = is.serializeIdentifiers();
    int* sortstrstore_buf = ssa.serialize();
    int* sortstore_buf = sa.serialize();

    assert(sizeof(SRef) == sizeof(int));

    int idstore_buf_sz = idstore_buf[0];
    int sortstrstore_buf_sz = sortstrstore_buf[0];
    int sortstore_buf_sz = sortstore_buf[0];

    // buffer size, pointers to the buffer starts and the size for sorts = 6
    int buf_sz = idstore_buf_sz + sortstrstore_buf_sz
                        + sortstore_buf_sz + sorts.size() + 6;
    buf = (int*)malloc(buf_sz * sizeof(int));

    buf[0] = buf_sz;

    int idstore_buf_offs = 5;
    int sortstrstore_buf_offs = idstore_buf_offs+idstore_buf_sz;
    int sortstore_buf_offs = sortstrstore_buf_offs + sortstrstore_buf_sz;
    int sorts_offs = sortstore_buf_offs + sortstore_buf_sz;
    buf[1] = idstore_buf_offs;
    buf[2] = sortstrstore_buf_offs;
    buf[3] = sortstore_buf_offs;
    buf[4] = sorts_offs;

    for (int i = 0; i < idstore_buf_sz; i++)
        buf[idstore_buf_offs+i] = idstore_buf[i];
    for (int i = 0; i < sortstrstore_buf_sz; i++)
        buf[sortstrstore_buf_offs+i] = sortstrstore_buf[i];
    for (int i = 0; i < sortstore_buf_sz; i++)
        buf[sortstore_buf_offs+i] = sortstore_buf[i];

    buf[sorts_offs] = sorts.size();
    for (int i = 0; i < sorts.size(); i++)
        buf[sorts_offs+1+i] = sorts[i].x;

    free(idstore_buf);
    free(sortstrstore_buf);
    free(sortstore_buf);

    return buf;
}

void SStore::deserializeSorts(const int* buf)
{
    int idstore_buf_offs     = buf[1];
    int sortstrstore_buf_offs= buf[2];
    int sortstore_buf_offs   = buf[3];
    int sorts_offs           = buf[4];

    is.deserializeIdentifiers(&buf[idstore_buf_offs]);
    ssa.deserialize(&buf[sortstrstore_buf_offs]);
    sa.deserialize(&buf[sortstore_buf_offs]);

    for (int i = sorts_offs+1; i < buf[sorts_offs]; i++) {
        sorts.push(SRef({(uint32_t)buf[i]}));
        char* canon_name;
        asprintf(&canon_name, "%s", is.getName((operator[] (sorts.last()))->getCar()));
        sortTable.insert(canon_name, sorts.last());
    }

}

