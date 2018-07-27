#include "LABounds.h"
#include "LRALogic.h"

LABound::LABound(BoundT type, PtAsgn leq_pta, LVRef var, const Delta& delta)
    : type(type.t)
    , reverse(false)
    , active(true)
    , idx(UINT32_MAX)
    , leq_pta(leq_pta)
    , var(var)
    , delta(delta)
{}

LABoundRef LABoundAllocator::alloc(BoundT type, PtAsgn leq_pta, LVRef var, const Delta& delta)
{
    uint32_t v = RegionAllocator<uint32_t>::alloc(laboundWord32Size());
    LABoundRef id = {v};
    new (lea(id)) LABound(type, leq_pta, var, delta);
    return id;
}

LABoundList::LABoundList(LVRef v, const vec<LABoundRef>& bs)
    : v(v)
    , reloc(0)
    , sz(bs.size())
{
    for (int i = 0; i < bs.size(); i++)
        bounds[i] = bs[i];
}

void LABoundListAllocator::moveTo(LABoundListAllocator& to)
{
    to.n_boundlists = n_boundlists;
    RegionAllocator<uint32_t>::moveTo(to);
}

LABoundListRef LABoundListAllocator::alloc(const LVRef v, const vec<LABoundRef>& bs)
{
    uint32_t b = RegionAllocator<uint32_t>::alloc(boundlistWord32Size(bs.size()));
    LABoundListRef id = {b};
    new (lea(id)) LABoundList(v, bs);
    return id;
}

LABoundListRef LABoundListAllocator::alloc(LABoundList& from)
{
    vec<LABoundRef> tmp;
    for (int i = 0; i < from.size(); i++)
        tmp.push(from[i]);
    return alloc(from.getVar(), tmp);
}

void LABoundListAllocator::free(LABoundListRef tid)
{
    LABoundList& b = operator[](tid);
    RegionAllocator<uint32_t>::free(boundlistWord32Size(b.size()));
}

void LABoundListAllocator::reloc(LABoundListRef& tr, LABoundListAllocator& to)
{
    LABoundList& bl = operator[](tr);
    if (bl.reloced()) { tr = bl.relocation(); return; }
    tr = to.alloc(bl);
    bl.relocate(tr);
    to[tr].sz = bl.size();
    to[tr].v  = bl.getVar();
}

LABoundStore::BoundInfo LABoundStore::addBound(PTRef leq_ref)
{
//    printf(" -> bound store gets %s\n", logic.pp(leq_ref));
    Pterm& leq = logic.getPterm(leq_ref);
    PTRef const_tr = leq[0];
    PTRef sum_tr = leq[1];

    bool sum_term_is_negated = logic.isNegated(sum_tr);

    PTRef pos_sum_tr = sum_term_is_negated ? logic.mkNumNeg(sum_tr) : sum_tr;

    LVRef v = lavarStore.getVarByPTId(logic.getPterm(pos_sum_tr).getId());

    LABoundRef br_pos;
    LABoundRef br_neg;

    if (sum_term_is_negated) {
        opensmt::Real constr_neg = -logic.getNumConst(const_tr);
        br_pos = ba.alloc(bound_u, PtAsgn(leq_ref, l_True), v, Delta(constr_neg));
        br_neg = ba.alloc(bound_l, PtAsgn(leq_ref, l_False), v, Delta(constr_neg, 1));
    }
    else {
        const Real& constr = logic.getNumConst(const_tr);
        br_pos = ba.alloc(bound_l, PtAsgn(leq_ref, l_True), v, Delta(constr));
        br_neg = ba.alloc(bound_u, PtAsgn(leq_ref, l_False), v, Delta(constr, -1));
    }

//    printf(" --> %s\n", printBound(br_pos));
//    printf(" --> %s\n", printBound(br_neg));
    BoundInfo bi{v, br_pos, br_neg, leq.getId()};
    in_bounds.push(bi);
    return bi;
}

void LABoundStore::updateBound(PTRef tr)
{
    // Check if the bound already exists.  If so, don't do anything.
    if ((ptermToLABoundsRef.size() > Idx(logic.getPterm(tr).getId())) &&
            !(ptermToLABoundsRef[Idx(logic.getPterm(tr).getId())] == LABoundRefPair{LABoundRef_Undef, LABoundRef_Undef}))
        return;

    BoundInfo bi = addBound(tr);
    LVRef vr = bi.v;
    while (ptermToLABoundsRef.size() <= Idx(bi.leq_id))
        ptermToLABoundsRef.push({ LABoundRef_Undef, LABoundRef_Undef });

    ptermToLABoundsRef[Idx(bi.leq_id)] = { bi.b1, bi.b2 };
    // Fix this to do a linear traverse
    vec<LABoundRef> new_bounds;
    LABoundListRef blr = var_bound_lists[lva[vr].ID()];

    for (int i = 0; i < bla[blr].size(); i++)
        new_bounds.push(bla[blr][i]);

    new_bounds.push(bi.b1);
    new_bounds.push(bi.b2);

    LABoundListRef br = bla.alloc(vr, new_bounds);
    var_bound_lists[lva[vr].ID()] = br;
    sort<LABoundRef,bound_lessthan>(bla[br].bounds, bla[br].size(), bound_lessthan(ba));

    for (int j = 0; j < bla[br].size(); j++)
        ba[bla[br][j]].setIdx(j);
}

void LABoundStore::buildBounds(vec<LABoundRefPair>& ptermToLABoundRefs)
{
    VecMap<LVRef, BoundInfo, LVRefHash> bounds_map;

    for (int i = 0; i < in_bounds.size(); i++) {
        LVRef v = in_bounds[i].v;
        if (!bounds_map.has(v))
            bounds_map.insert(v, vec<BoundInfo>());
        bounds_map[v].push(in_bounds[i]);
        while (ptermToLABoundsRef.size() <= Idx(in_bounds[i].leq_id))
            ptermToLABoundsRef.push({ LABoundRef_Undef, LABoundRef_Undef });
        ptermToLABoundsRef[Idx(in_bounds[i].leq_id)] = { in_bounds[i].b1, in_bounds[i].b2 };
    }
    vec<LVRef> keys;
    bounds_map.getKeys(keys);
    for (int i = 0; i < keys.size(); i++) {
        vec<LABoundRef> refs;
        LABoundRef lb_minusInf = ba.alloc(bound_l, PtAsgn(logic.getTerm_true(), l_True), keys[i], Delta_MinusInf);
        LABoundRef ub_plusInf = ba.alloc(bound_u, PtAsgn(logic.getTerm_true(), l_True), keys[i], Delta_PlusInf);
        refs.push(lb_minusInf);
        refs.push(ub_plusInf);
        for (int j = 0; j < bounds_map[keys[i]].size(); j++) {
            BoundInfo &info = bounds_map[keys[i]][j];
            refs.push(info.b1);
            refs.push(info.b2);
        }
        LABoundListRef br = bla.alloc(keys[i], refs);

        while (var_bound_lists.size() <= lva[keys[i]].ID())
            var_bound_lists.push(LABoundListRef_Undef);
        var_bound_lists[lva[keys[i]].ID()] = br;
        sort<LABoundRef,bound_lessthan>(bla[br].bounds, bla[br].size(), bound_lessthan(ba));

        for (int j = 0; j < bla[br].size(); j++)
            ba[bla[br][j]].setIdx(j);

        // Check that the bounds are correctly ordered
#ifdef DO_BOUNDS_CHECK
        vec<LABoundRef> lowerbounds;
        vec<LABoundRef> upperbounds;
        for (int j = 1; j < bla[br].size() - 1; j++) {
            LABoundRef tmp = bla[br].bounds[j];
            if (ba[tmp].getType() == bound_l)
                lowerbounds.push(tmp);
            else
                upperbounds.push(tmp);
        }
        for (int j = 0; j < lowerbounds.size()-1; j++) {
            LABoundRef bound_higher = lowerbounds[j+1];
            LABoundRef bound_lower = lowerbounds[j];
            PTRef ref_higher = ba[bound_higher].getSign() == l_False ? logic.mkNot(ba[bound_higher].getPTRef()) : ba[bound_higher].getPTRef();
            PTRef ref_lower = ba[bound_lower].getSign() == l_False ? logic.mkNot(ba[bound_lower].getPTRef()) : ba[bound_lower].getPTRef();
//            printf("Checking that %s -> %s\n", printBound(bound_higher), printBound(bound_lower));
            logic.implies(ref_higher, ref_lower);
        }
        for (int j = 0; j < upperbounds.size()-1; j++) {
            LABoundRef bound_higher = upperbounds[j+1];
            LABoundRef bound_lower = upperbounds[j];
            PTRef ref_higher = ba[bound_higher].getSign() == l_False ? logic.mkNot(ba[bound_higher].getPTRef()) : ba[bound_higher].getPTRef();
            PTRef ref_lower = ba[bound_lower].getSign() == l_False ? logic.mkNot(ba[bound_lower].getPTRef()) : ba[bound_lower].getPTRef();
//            printf("Checking that %s -> %s\n", printBound(bound_lower), printBound(bound_higher));
            logic.implies(ref_lower, ref_higher);
        }
#endif

    }

    // make sure all variables have at least the trivial bounds
    for (int i = 0; i < lavarStore.numVars(); i++) {
        LVRef vr = lavarStore.getVarByIdx(i);
        LAVar& v = lva[vr];
        while (var_bound_lists.size() <= v.ID())
            var_bound_lists.push(LABoundListRef_Undef);

        if (var_bound_lists[v.ID()] == LABoundListRef_Undef) {
            vec<LABoundRef> refs;
            LABoundRef lb_minusInf = ba.alloc(bound_l, PtAsgn(logic.getTerm_true(), l_True), vr, Delta_MinusInf);
            LABoundRef ub_plusInf = ba.alloc(bound_u, PtAsgn(logic.getTerm_true(), l_True), vr, Delta_PlusInf);
            refs.push(lb_minusInf);
            refs.push(ub_plusInf);
            LABoundListRef br = bla.alloc(vr, refs);
            var_bound_lists[v.ID()] = br;
        }
    }
}

LABoundRef
LABoundList::operator[](int i) const
{
    return bounds[i];
}

// Debug

char*
LABoundStore::printBound(LABoundRef br) const
{
    char *str_out;
    char *v_str_ptr = logic.pp(lva[ba[br].getLVRef()].getPTRef());
    char *v_str_lvr = lva.printVar(ba[br].getLVRef());
    char* v_str;
    asprintf(&v_str, "%s [%s]", v_str_lvr, v_str_ptr);
    free(v_str_lvr);
    free(v_str_ptr);
    const Delta & d = ba[br].getValue();
    if (d.isMinusInf())
        asprintf(&str_out, "- Inf <= %s", v_str);
    else if (d.isPlusInf())
        asprintf(&str_out, "%s <= + Inf", v_str);
    else {
        opensmt::Real r = d.R();
        opensmt::Real s = d.D();
        BoundT type = ba[br].getType();
        if ((type == bound_l) && (s == 0))
            asprintf(&str_out, "%s <= %s", r.get_str().c_str(), v_str);
        if ((type == bound_l) && (s != 0))
            asprintf(&str_out, "%s < %s", r.get_str().c_str(), v_str);
        if ((type == bound_u) && (s == 0))
            asprintf(&str_out, "%s <= %s", v_str, r.get_str().c_str());
        if ((type == bound_u) && (s != 0))
            asprintf(&str_out, "%s < %s", v_str, r.get_str().c_str());
    }
    free(v_str);

    return str_out;
}

char* LABoundStore::printBounds(LVRef v) const
{
    LABoundListRef blr = var_bound_lists[lva[v].ID()];
    char* bounds_str = (char*) malloc(1);
    bounds_str[0] = '\0';
    for (int i = 0; i < bla[blr].size(); i++) {
        LABoundRef br = bla[blr][i];
        char* tmp;
        char* tmp2 = printBound(br);
        asprintf(&tmp, "%s(%s) ", bounds_str, tmp2);
        free(bounds_str);
        free(tmp2);
        bounds_str = tmp;
    }
    return bounds_str;
}

LABoundRefPair LABoundStore::getBoundRefPair(const PTRef leq)
{ return ptermToLABoundsRef[Idx(logic.getPterm(leq).getId())]; }


int LABoundAllocator::laboundWord32Size() {
    return (sizeof(LABound)) / sizeof(uint32_t); }

inline unsigned LABoundAllocator::getNumBounds() const { return n_bounds; }

inline LABound&       LABoundAllocator::operator[](LABoundRef r)       { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
inline const LABound& LABoundAllocator::operator[](LABoundRef r) const { return (LABound&)RegionAllocator<uint32_t>::operator[](r.x); }
inline LABound*       LABoundAllocator::lea       (LABoundRef r)       { return (LABound*)RegionAllocator<uint32_t>::lea(r.x); }
inline const LABound* LABoundAllocator::lea       (LABoundRef r) const { return (LABound*)RegionAllocator<uint32_t>::lea(r.x); }
inline LABoundRef     LABoundAllocator::ael       (const LABound* t)   { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); LABoundRef rf; rf.x = r; return rf; }

inline bool           LABoundList::reloced   ()                 const { return reloc; }
inline LABoundListRef LABoundList::relocation()                 const { return reloc_target; }
inline void           LABoundList::relocate  (LABoundListRef r)       { reloc = 1; reloc_target = r; }
inline unsigned       LABoundList::size      ()                 const { return sz; }

inline LVRef          LABoundList::getVar    ()                 const { return v; }

inline bool bound_lessthan::operator() (LABoundRef r1, LABoundRef r2) const { return ba[r1].getValue() < ba[r2].getValue(); }

int LABoundListAllocator::boundlistWord32Size(int size) {
    return (sizeof(LABoundList) + (sizeof(LABoundRef)*size)) / sizeof(uint32_t); }

inline LABoundList&       LABoundListAllocator::operator[](LABoundListRef r)       { return (LABoundList&)RegionAllocator<uint32_t>::operator[](r.x); }
inline const LABoundList& LABoundListAllocator::operator[](LABoundListRef r) const { return (LABoundList&)RegionAllocator<uint32_t>::operator[](r.x); }
inline LABoundList*       LABoundListAllocator::lea(LABoundListRef r)              { return (LABoundList*)RegionAllocator<uint32_t>::lea(r.x); }
inline const LABoundList* LABoundListAllocator::lea(LABoundListRef r) const        { return (LABoundList*)RegionAllocator<uint32_t>::lea(r.x); }
inline LABoundListRef     LABoundListAllocator::ael(const LABoundList* t)          { RegionAllocator<uint32_t>::Ref r = RegionAllocator<uint32_t>::ael((uint32_t*)t); LABoundListRef rf; rf.x = r; return rf; }

//inline LABound& LABoundStore::operator[] (LABoundRef br) { return ba[br]; }
LABoundListRef LABoundStore::getBounds(LVRef v) const { return var_bound_lists[lva[v].ID()]; }
LABoundRef LABoundStore::getBoundByIdx(LVRef v, int it) const { return bla[getBounds(v)][it]; }
int LABoundStore::getBoundListSize(LVRef v) { return bla[getBounds(v)].size(); }
bool LABoundStore::isUnbounded(LVRef v) const { return ( (bla[getBounds(v)].size() == 2) && (ba[bla[getBounds(v)][0]].getValue().isMinusInf()) && (ba[bla[getBounds(v)][1]].getValue().isPlusInf()) ); }
