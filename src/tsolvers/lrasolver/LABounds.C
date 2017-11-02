#include "LABounds.h"

LABound::LABound(BoundT type, PtAsgn leq_pta, const Delta& delta)
    : type(type.t)
    , reverse(false)
    , active(true)
    , idx(536870911)
    , leq_pta(leq_pta)
    , delta(delta)
{}

LABoundRef LABoundAllocator::alloc(BoundT type, PtAsgn leq_pta, const Delta& delta)
{
    uint32_t v = RegionAllocator<uint32_t>::alloc(laboundWord32Size());
    LABoundRef id = {v};
    new (lea(id)) LABound(type, leq_pta, delta);
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
    LABoundRef br_pos = ba.alloc(bound_t, PtAsgn(leq_ref, l_True), Delta(constr));
    LABoundRef br_neg;

    if (bound_t == bound_u)
        br_neg = ba.alloc(~bound_t, PtAsgn(leq_ref, l_False), Delta(constr, 1));
    else
        br_neg = ba.alloc(~bound_t, PtAsgn(leq_ref, l_False), Delta(constr, -1));

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
        while (ptermToLABoundsRef.size() <= in_bounds[i].leq_id)
            ptermToLABoundsRef.push({ LABoundRef_Undef, LABoundRef_Undef });
        ptermToLABoundsRef[in_bounds[i].leq_id] = { in_bounds[i].b1, in_bounds[i].b2 };
    }
    vec<LVRef> keys;
    bounds_map.getKeys(keys);
    for (int i = 0; i < keys.size(); i++) {
        vec<LABoundRef> refs;
        for (int j = 0; j < bounds_map[keys[i]].size(); i++) {
            BoundInfo &info = bounds_map[keys[i]][j];
            refs.push(info.b1);
            refs.push(info.b2);
        }
        LABoundListRef br = bla.alloc(keys[i], refs);
        sort<LABoundRef,bound_lessthan>(bla[br].bounds, bla[br].size(), bound_lessthan(ba));
        for (int j = 0; j < bla[br].size(); j++)
            ba[bla[br][j]].setIdx(j);
    }
}


