//
// Created by Antti on 31.03.21.
//

#include "SplitData.h"

int SplitData::getLitSize(Lit l)
{
    int sz = 0;
    if (sign(l)) sz++;
    Var v = var(l);
    int n = v+1;
    while (n != 0) { n /= 10; sz++; }
    return sz;
}

char* SplitData::litToString(const Lit l)
{
    char* l_str;
    asprintf(&l_str, "%s%d", sign(l) ? "-" : "", var(l)+1);
    return l_str;
}

template<class C>
char* SplitData::clauseToString(const C& c)
{
    char* c_str = (char*)malloc(1);
    c_str[0] = 0;
    char* c_old = c_str;
    for (int i = 0; i < c.size(); i++)
    {
        char* l_str = litToString(c[i]);
        c_old = c_str;
        asprintf(&c_str, "%s%s ", c_old, l_str);
        free(l_str);
        free(c_old);
    }
    c_old = c_str;
    asprintf(&c_str, "%s0", c_str);
    free(c_old);
    return c_str;
}

char* SplitData::splitToString()
{
    int buf_cap = 1024;
    int sz = 0;
    char* buf = (char*) malloc(1024);

    // The constraints
    for (const vec<Lit>& c : constraints) {
        for (Lit l : c) {
            int n = getLitSize(l);
            while (buf_cap < sz + n + 2)   // Lit, space, and NULL
            {
                buf_cap *= 2;
                buf = (char*) realloc(buf, buf_cap);
            }
            sprintf(&buf[sz], "%s%d ", sign(l) ? "-" : "", var(l)+1);
            sz += n+1; // Points to the NULL
        }
        while (buf_cap < sz + 3)   // 0, newline, and NULL
        {
            buf_cap *= 2;
            buf = (char*) realloc(buf, buf_cap);
        }
        sprintf(&buf[sz], "0\n");
        sz += 2;
    }

    for (const vec<Lit> & c : learnts) {
        for (Lit l : c) {
            int n = getLitSize(l);
            while (buf_cap < sz + n + 2)   // The size of lit, space, and NULL
            {
                buf_cap *= 2;
                buf = (char*) realloc(buf, buf_cap);
            }
            sprintf(&buf[sz], "%s%d ", sign(l) ? "-" : "", var(l)+1);
            sz += n+1; // points to the null
        }
        while (buf_cap < sz + 3)   // The zero, newline, and the NULL
        {
            buf_cap *= 2;
            buf = (char*) realloc(buf, buf_cap);
        }
        sprintf(&buf[sz], "0\n");
        sz += 2; // Points to the NULL
    }
    buf = (char*) realloc(buf, sz+1);
    return buf;
}

void SplitData::toPTRefs(std::vector<vec<PtAsgn>>& out, const std::vector<vec<Lit>>& in, const THandler& theory_handler)
{
    for (const vec<Lit>& c : in) {
        out.emplace_back();
        vec<PtAsgn>& out_clause = out[out.size()-1];
        for (Lit l : c)
        {
            PTRef tr = theory_handler.varToTerm(var(l));
            PtAsgn pta(tr, sign(l) ? l_False : l_True);
            out_clause.push(pta);
        }
    }
}
