//
//
//

#include "LARefs.h"
#include "Polynomials.h"
#include "BindedRows.h"
PolyTermList::PolyTermList(PolyTermList &old, int new_cap) : cap(new_cap), sz(old.sz)
{
    for (int i = 0; i < old.size(); i++)
        terms[i] = old.terms[i];
}

PolyTermList::PolyTermList(vec<PolyTermRef>& ps) {
    cap = sz = ps.size();
    for (int i = 0; i < ps.size(); i++)
        terms[i] = ps[i];
}

//
// Update the polynomial, positions, and binded rows.
//
void
PolyStore::remove(LVRef v, PolyRef pol)
{
    brs.remove(pol, v);

    Map<LVRef,int,LVRefHash>& positions = varToIdx[pa[pol].getId()];
    int start_idx = positions[v]+1;
    positions.remove(v);
    for (int i = start_idx; i < getSize(pol); i++) {
        LVRef w = pta[readTerm(pol, i)].var;
        positions[w] = i-1;
        writeTerm(pol, i-1, readTerm(pol, i));
        brs.remove(pol, w);
        brs.add(pol, i-1, w);
    }
    ptla[pa[pol].getTerms()].sz --;
    assert(positions.getSize() == ptla[pa[pol].getTerms()].sz);
//    checkConsistency(pol);
}

void PolyStore::remove(LVRef poly_var)
{
    remove(lva[poly_var].getPolyRef());
}

void
PolyStore::remove(PolyRef pr)
{
    for (int i = 0; i < getSize(pr); i++) {
        brs.remove(pr, pta[readTerm(pr, i)].var);
    }
    for (int i = 0; i < getSize(pr); i++) {
        // Remove the PolyTermRef
        PolyTermRef ptr = readTerm(pr, i);
        pta.free(ptr);
    }
    ptla.free(pa[pr].getTerms());
    pa.free(pr);
}

void
PolyStore::add(PolyRef pr, PolyTermRef ptr)
{
    add(pr, pta[ptr].var, pta[ptr].coef);
}

void
PolyStore::add(PolyRef pr, LVRef v, const Real &c) {
    int pos;
    Poly& poly = pa[pr];
    LVRef poly_var = poly.getVar();
    Map<LVRef,int,LVRefHash>& positions = varToIdx[poly.getId()];
    if (positions.has(v)) {
        pos = positions[v];
        PolyTermRef v_term = readTerm(pr, positions[v]);
        pta.updateCoef(v_term, pta[v_term].coef + c);
        if (pta[v_term].coef == 0) {
            pta.free(v_term);
            remove(v, pr);
            pos = -1;
        }
    }
    else {
        PolyTermListRef terms = pa[pr].getTerms();
        PolyTermListRef tr_new = terms;
        if (ptla[terms].getUnusedCap() == 0) {
            // We need to allocate a new polynomial with bigger capacity.
            tr_new = ptla.alloc(terms, ptla[terms].size() > 0 ? ptla[terms].size() * 2 : 1);
            poly.updateTermRef(tr_new);
            ptla.free(terms);
        }

        PolyTermList& t_new = ptla[tr_new];
        t_new.append(pta.alloc(c, v), v);
        pos = t_new.size()-1;
        positions.insert(v, pos);
        brs.add(pr, pos, v);
//        assert(checkConsistency(pr));
    }
}



void PolyStore::updateTerm(PolyRef pr, PolyTermRef term, LVRef var, const opensmt::Real& coef) {
    LVRef old_var = pta[term].var;
    pta.updateVar(term, var);
    pta.updateCoef(term, coef);
    Map<LVRef, int, LVRefHash> &positions = varToIdx[pa[pr].getId()];
    int idx = positions[old_var];
    positions.remove(old_var);
    positions.insert(var, idx);
    brs.remove(pr, old_var);
    brs.add(pr, idx, var);
    checkConsistency(pr);
}

char* PolyStore::printPolyTerm(const opensmt::Real &coef, LVRef var)
{
    if (coef == 1)
        return lva.printVar(var);

    char *buf;
    if (coef == -1)
        asprintf(&buf, "-%s", lva.printVar(var));
    else {
        const char *coef_str = coef.get_str().c_str();
        asprintf(&buf, "(* %s %s)", coef_str, lva.printVar(var));
    }
    return buf;
}

char* PolyStore::printPolyTerm(const PolyTermRef ptr)
{
    return printPolyTerm(pta[ptr].coef, pta[ptr].var);
}

char* PolyStore::printPoly(PolyRef pr)
{
    Poly &p = pa[pr];
    char *buf = NULL;
    for (int i = 0; i < getSize(pr); i++) {
        char *buf_new;
        const PolyTerm& pt = pta[readTerm(pr, i)];
        asprintf(&buf_new, "%s %s", (buf == NULL ? "" : buf), printPolyTerm(pt.coef, pt.var));
        free(buf);
        buf = buf_new;
    }
    char *buf_new;
    asprintf(&buf_new, "%s = (+%s)", lva.printVar(p.var), buf == NULL ? "" : buf);
    free(buf);
    return buf_new;
}

char* PolyStore::printOccurrences(LVRef var)
{
    char* buf = NULL;
    char *buf_new;
    BindedRows& b = brs.getBindedRows(var);
    for (int i = 0; i < b.size(); i++) {
        asprintf(&buf_new, "%s (%s, pos %d)", (buf == NULL ? "" : buf), printPoly(b[i].poly), b[i].pos);
        free(buf);
        buf = buf_new;
    }
    asprintf(&buf_new, "(%s)", buf == NULL ? "" : buf);
    free(buf);
    return buf_new;
}

PolyRef
PolyStore::makePoly(LVRef s, vec<PolyTermRef>& terms)
{
    PolyTermListRef ptlr = ptla.alloc(terms);
    PolyRef pr = pa.alloc(ptlr, s);
    lva[s].setPolyRef(pr);
    assert(pa[pr].getId() == varToIdx.size());
    varToIdx.push();
    Map<LVRef,int,LVRefHash>& positions = varToIdx.last();
    for (int i = 0; i < terms.size(); i++) {
        positions.insert(pta[terms[i]].var, i);
        brs.add(pr, i, pta[terms[i]].var);
    }
//    printf("Made the poly %s from PTRef %s\n", printPoly(pr), logic.pp(lva[s].getPTRef()));
//    checkConsistency(pr);
    return pr;
}

bool PolyStore::checkConsistency(PolyRef pr)
{
    Poly& p = pa[pr];
    Map<LVRef,int,LVRefHash>& positions = varToIdx[pa[pr].getId()];
    for (int i = 0; i < getSize(pr); i++) {
        LVRef prs_var = pta[readTerm(pr, i)].var;
        if (positions[prs_var] != i) {
            assert(false);
            return false;
        }
        BindedRows& rows_binded_to_prs_var = brs.getBindedRows(prs_var);
        for (int j = 0; j < rows_binded_to_prs_var.size(); j++) {
            BindedRow r = rows_binded_to_prs_var[j];
            if (r.poly== pr) {
                if (r.pos != i) {
                    assert(false);
                    return false;
                }
            }
        }
    }
    return true;
}
