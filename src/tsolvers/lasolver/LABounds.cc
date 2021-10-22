#include "LABounds.h"
#include "Map.h"
#include "Sort.h"

LABound::LABound(BoundT type, LVRef var, Delta && delta, int id)
    : type(type.t)
    , bidx(UINT32_MAX)
    , id(id)
    , var(var)
    , delta(std::move(delta))
{}

LABoundRef LABoundAllocator::alloc(BoundT type, LVRef var, Delta && delta)
{
    uint32_t v = RegionAllocator<uint32_t>::alloc(laboundWord32Size());
    LABoundRef id = {v};
    new (lea(id)) LABound(type, var, std::move(delta), static_cast<int>(allocatedBounds.size()));
    allocatedBounds.push_back(id);
    return id;
}

// Debug

char*
LABoundStore::printBound(LABoundRef br) const
{
    char *str_out;
    char *v_str_lvr;
    int written = asprintf(&v_str_lvr, "v%d", ba[br].getLVRef().x);
    assert(written >= 0);
    char* v_str;
    written = asprintf(&v_str, "%s", v_str_lvr);
    assert(written >= 0); (void)written;
    free(v_str_lvr);
    const Delta & d = ba[br].getValue();

    opensmt::Real r = d.R();
    opensmt::Real s = d.D();
    BoundT type = ba[br].getType();
    if ((type == bound_l) && (s == 0))
        written = asprintf(&str_out, "%s <= %s", r.get_str().c_str(), v_str);
    if ((type == bound_l) && (s != 0))
        written = asprintf(&str_out, "%s < %s", r.get_str().c_str(), v_str);
    if ((type == bound_u) && (s == 0))
        written = asprintf(&str_out, "%s <= %s", v_str, r.get_str().c_str());
    if ((type == bound_u) && (s != 0))
        written = asprintf(&str_out, "%s < %s", v_str, r.get_str().c_str());

    assert(written >= 0); (void)written;
    free(v_str);

    return str_out;
}

char* LABoundStore::printBounds(LVRef v) const
{
    auto const & var_bounds = getBounds(v);
    char* bounds_str = (char*) malloc(1);
    bounds_str[0] = '\0';
    for (unsigned int i = 0; i < var_bounds.size_(); i++) {
        LABoundRef br = var_bounds[i];
        char* tmp;
        char* tmp2 = printBound(br);
        int written = asprintf(&tmp, "%s(%s) ", bounds_str, tmp2);
        assert(written >= 0); (void)written;
        free(bounds_str);
        free(tmp2);
        bounds_str = tmp;
    }
    return bounds_str;
}

inline bool bound_lessthan::operator() (LABoundRef r1, LABoundRef r2) const { return ba[r1].getValue() < ba[r2].getValue(); }

LABoundRef LABoundStore::getBoundByIdx(LVRef v, int idx) const {
    auto const & var_bounds = getBounds(v);
    assert(idx < var_bounds.size());
    return var_bounds[idx];
}
bool LABoundStore::isUnbounded(LVRef v) const { return getBounds(v).size() == 0; }

void LABoundStore::clear() {
    this->ba.clear();
    this->in_bounds.clear();
    this->bounds.clear();
}

void LABoundStore::updateBound(BoundInfo bi) {
    auto & varBounds = getBounds(bi.v);
    for (LABoundRef bound : {bi.ub, bi.lb}) {
        unsigned idx = varBounds.size();
        varBounds.push(bound);
        bound_lessthan lessthan(ba);
        for (; idx > 0; --idx) {
            if (lessthan(varBounds[idx - 1], varBounds[idx])) {
                break;
            }
            std::swap(varBounds[idx - 1], varBounds[idx]);
            ba[varBounds[idx]].setIdx(LABound::BLIdx{idx});
        }
        assert(varBounds[idx] == bound);
        ba[varBounds[idx]].setIdx(LABound::BLIdx{idx});
    }
    // Post-condition; indices must correspond to the place in the bound list
    assert([&](){
        for (unsigned i = 0; i < varBounds.size_(); ++i) {
            if (ba[varBounds[i]].getIdx().x != i) { return false; }
        }
        return true;
    }());
}

void LABoundStore::buildBounds()
{
    VecMap<LVRef, BoundInfo, LVRefHash> bounds_map;

    for (int i = 0; i < in_bounds.size(); i++) {
        LVRef v = in_bounds[i].v;
        if (!bounds_map.has(v)) {
            bounds_map.insert(v, vec<BoundInfo>());
        }
        bounds_map[v].push(in_bounds[i]);
    }
    vec<LVRef> keys;
    bounds_map.getKeys(keys);
    for (LVRef v : keys) {
        vec<LABoundRef> refs;
        vec<BoundInfo> const & boundInfos = bounds_map[v];
        for (BoundInfo const & info : boundInfos) {
            refs.push(info.ub);
            refs.push(info.lb);
        }

        sort<LABoundRef,bound_lessthan>(refs, refs.size(), bound_lessthan(ba));
        for (unsigned j = 0; j < refs.size_(); ++j) {
            ba[refs[j]].setIdx(LABound::BLIdx{j});
        }

        while (bounds.size() <= getVarId(v)) {
            bounds.emplace_back();
        }
        refs.moveTo(bounds.at(getVarId(v)));
    }

    // make sure all variables are recorded in the bound lists, even if they have no bounds
    for (LVRef ref : lvstore) {
        auto id = getVarId(ref);
        while (bounds.size() <= id) {
            bounds.emplace_back();
        }
    }
}
