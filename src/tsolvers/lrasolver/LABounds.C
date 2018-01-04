#include "LABounds.h"


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

void LABoundStore::addBound(LVRef v, PTRef leq_ref, PTId leq_id, const Real& constr, BoundT bound_t)
{
    printf(" -> bound store gets %s\n", logic.pp(leq_ref));
    LABoundRef br_pos = ba.alloc( bound_t, PtAsgn(leq_ref, l_True) , v, bound_t == bound_u ? Delta(-constr)   : Delta(constr));
    LABoundRef br_neg = ba.alloc(~bound_t, PtAsgn(leq_ref, l_False), v, bound_t == bound_u ? Delta((-constr), 1) : Delta(constr, -1));
    printf(" --> %s\n", printBound(br_pos));
    printf(" --> %s\n", printBound(br_neg));
//    LABoundRef br_neg = ba.alloc(~bound_t, PtAsgn(leq_ref, l_False), v, bound_t == bound_u ? Delta(constr, 1) : Delta((-constr), -1));
    // Delta(constr, bound_t == bound_u ? 1 : -1));

//    if (bound_t == bound_u)
//        br_neg = ba.alloc(~bound_t, PtAsgn(leq_ref, l_False), v, Delta(constr, 1));
//    else
//        br_neg = ba.alloc(~bound_t, PtAsgn(leq_ref, l_False), v, Delta(constr, -1));

    in_bounds.push(BoundInfo{v, br_pos, br_neg, leq_id});
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
            printf("Checking that %s -> %s\n", printBound(bound_higher), printBound(bound_lower));
            logic.implies(ref_higher, ref_lower);
        }
        for (int j = 0; j < upperbounds.size()-1; j++) {
            LABoundRef bound_higher = upperbounds[j+1];
            LABoundRef bound_lower = upperbounds[j];
            PTRef ref_higher = ba[bound_higher].getSign() == l_False ? logic.mkNot(ba[bound_higher].getPTRef()) : ba[bound_higher].getPTRef();
            PTRef ref_lower = ba[bound_lower].getSign() == l_False ? logic.mkNot(ba[bound_lower].getPTRef()) : ba[bound_lower].getPTRef();
            printf("Checking that %s -> %s\n", printBound(bound_lower), printBound(bound_higher));
            logic.implies(ref_lower, ref_higher);
        }
#endif

    }
    for (int i = 0; i < lavarStore.numVars(); i++) {
        LAVar& v = lva[lavarStore.getVarByIdx(i)];
        if (var_bound_lists[v.ID()] == LABoundListRef_Undef) {
            vec<LABoundRef> refs;
            LABoundRef lb_minusInf = ba.alloc(bound_l, PtAsgn(logic.getTerm_true(), l_True), keys[i], Delta_MinusInf);
            LABoundRef ub_plusInf = ba.alloc(bound_u, PtAsgn(logic.getTerm_true(), l_True), keys[i], Delta_PlusInf);
            refs.push(lb_minusInf);
            refs.push(ub_plusInf);
            LABoundListRef br = bla.alloc(keys[i], refs);
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
