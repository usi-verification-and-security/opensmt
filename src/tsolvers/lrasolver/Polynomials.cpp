//
//
//

#include "LARefs.h"
#include "Polynomials.h"
#include "BindedRows.h"
Poly::Poly(Poly &old, int new_cap)
{
    for (int i = 0; i < old.size(); i++) {
        terms[i] = old.terms[i];
    }
    id = old.id;
    cap = new_cap;
    sz = old.size();
}

Poly::Poly(vec<PolyTermRef>& ps, LVRef var, int id) : id(id), var(var) {
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
    Poly& p = pa[pol];
    LVRef poly_var = p.getVar();
    brs.remove(poly_var, v);

    Map<LVRef,int,LVRefHash>& positions = varToIdx[pa[pol].getId()];
    int start_idx = positions[v]+1;
    for (int i = start_idx; i < p.size(); i++) {
        LVRef v_old = pta[p[i-1]].var;
        positions.remove(v_old);
        LVRef new_var = pta[p[i]].var;
        int new_pos = i-1;
        positions.insert(new_var, new_pos);
        p[i - 1] = p[i];
        brs.remove(poly_var, new_var);
        brs.add(poly_var, new_pos, new_var);
    }
    p.sz --;
    checkConsistency(pol);
}

void
PolyStore::remove(LVRef poly_var)
{
    PolyRef pr = lva[poly_var].getPolyRef();
    for (int i = 0; i < pa[pr].size(); i++) {
        brs.remove(poly_var, pta[pa[pr][i]].var);
    }
    for (int i = 0; i < pa[pr].size(); i++) {
        // Remove the PolyTermRef
        PolyTermRef ptr = pa[pr][i];
        pta.free(ptr);
    }
    pa.free(pr);
}

int
PolyStore::add(PolyRef pr, LVRef v, Real &c) {
    assert(!lva[v].isBasic());
    int pos;
    Poly& poly = pa[pr];
    LVRef poly_var = poly.getVar();
    Map<LVRef,int,LVRefHash>& positions = varToIdx[poly.getId()];
    if (positions.has(v)) {
        pos = positions[v];
        PolyTermRef v_term = poly[positions[v]];
        pta.updateCoef(v_term, pta[v_term].coef + c);
        if (pta[v_term].coef == 0) {
            pta.free(v_term);
            brs.remove(poly.getVar(), v);
            remove(v, pr);
            pos = -1;
        }
    }
    else {
        PolyRef pr_new = pr;
        if (pa[pr].getUnusedCap() == 0) {
            // We need to allocate a new polynomial with bigger capacity.
            pr_new = pa.alloc(pr, poly.size() > 0 ? poly.size() * 2 : 1);
            lva[poly_var].setPolyRef(pr_new);
        }
        Poly& poly_upd = pa[pr_new];
        poly_upd.append(pta.alloc(c, v), v);
        pos = poly_upd.size();
        positions.insert(v, pos);
        printf("Adding occurrence of %s at pos %d on %s\n", lva.printVar(v), pos, printPoly(pr_new));
        brs.add(poly_var, pos, v);
        poly_upd.sz++;
        assert(checkConsistency(pr_new));
    }
    return pos;
}



void PolyStore::update(PolyRef pr, PolyTermRef old, LVRef var, const opensmt::Real& coef) {
    LVRef old_var = pta[old].var;
    pta.updateVar(old, var);
    pta.updateCoef(old, coef);
    Map<LVRef, int, LVRefHash> &positions = varToIdx[pa[pr].getId()];
    int idx = positions[old_var];
    positions.remove(old_var);
    positions.insert(var, idx);
    brs.remove(pa[pr].getVar(), old_var);
    brs.add(pa[pr].getVar(), idx, var);
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

char* PolyStore::printPoly(PolyRef pr)
{
    Poly &p = pa[pr];
    char *buf = NULL;
    for (int i = 0; i < p.size(); i++) {
        char *buf_new;
        const PolyTerm& pt = pta[p[i]];
        asprintf(&buf_new, "%s %s", (buf == NULL ? "" : buf), printPolyTerm(pt.coef, pt.var));
        free(buf);
        buf = buf_new;
    }
    char *buf_new;
    asprintf(&buf_new, "(+%s)", buf);
    free(buf);
    return buf_new;
}

PolyRef
PolyStore::makePoly(LVRef s, vec<PolyTermRef>& terms)
{
    PolyRef pr = pa.alloc(terms, s);
    lva[s].setPolyRef(pr);
    assert(pa[pr].getId() == varToIdx.size());
    varToIdx.push();
    Map<LVRef,int,LVRefHash>& positions = varToIdx.last();
    for (int i = 0; i < terms.size(); i++) {
        positions.insert(pta[terms[i]].var, i);
        brs.add(s, i, pta[terms[i]].var);
    }
    checkConsistency(pr);
    return pr;
}

bool PolyStore::checkConsistency(PolyRef pr)
{
    Poly& p = pa[pr];
    Map<LVRef,int,LVRefHash>& positions = varToIdx[pa[pr].getId()];
    for (int i = 0; i < p.size(); i++) {
        LVRef prs_var = pta[p[i]].var;
        if (positions[prs_var] != i) {
            assert(false);
            return false;
        }
        BindedRows& rows_binded_to_prs_var = brs.getBindedRows(prs_var);
        for (int j = 0; j < rows_binded_to_prs_var.size(); j++) {
            BindedRow r = rows_binded_to_prs_var[j];
            if (r.var == pa[pr].getVar()) {
                if (r.pos != i) {
                    assert(false);
                    return false;
                }
            }
        }
    }
    return true;
}
