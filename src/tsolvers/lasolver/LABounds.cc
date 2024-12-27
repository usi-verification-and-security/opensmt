#include "LABounds.h"

#include <minisat/mtl/Map.h>
#include <minisat/mtl/Sort.h>

namespace opensmt {

LABound::LABound(BoundT type, LVRef var, Delta && delta, int id)
    : type(type.t)
    , bidx(UINT32_MAX)
    , id(id)
    , var(var)
    , delta(std::move(delta))
{}

LABoundRef LABoundAllocator::alloc(BoundT type, LVRef var, Delta && delta)
{
    uint32_t v = RegionAllocator::alloc(laboundWord32Size());
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

    Real const & r = d.R();
    Real const & s = d.D();
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
    this->bounds.clear();
}

void LABoundStore::ensureReadyFor(LVRef v) {
    while (bounds.size() <= getVarId(v)) {
        bounds.emplace_back();
    }
}

LABoundStore::BoundInfo LABoundStore::allocBoundPair(LVRef v, BoundValuePair boundPair) {
    ensureReadyFor(v);
    LABoundRef ub = ba.alloc(bound_u, v, std::move(boundPair.upper));
    LABoundRef lb = ba.alloc(bound_l, v, std::move(boundPair.lower));
    auto & varBounds = bounds.at(getVarId(v));
    varBounds.push(ub);
    varBounds.push(lb);
    return BoundInfo{v, ub, lb};
}

LABoundStore::BoundInfo LABoundStore::allocBoundPairAndSort(LVRef v, BoundValuePair boundPair) {
    auto res = allocBoundPair(v, std::move(boundPair));

    // Get the two newly allocated bounds in the right position
    auto & varBounds = getBounds(v);
    assert(varBounds.size_() >= 2);
    unsigned indexToSort = varBounds.size_() - 2;
    for (unsigned index : {indexToSort, indexToSort + 1}) {
        [[maybe_unused]] const LABoundRef bound = varBounds[index];
        bound_lessthan lessthan(ba);
        while (index > 0 and not lessthan(varBounds[index - 1], varBounds[index])) {
            std::swap(varBounds[index - 1], varBounds[index]);
            ba[varBounds[index]].setIdx(LABound::BLIdx{index});
            --index;
        }
        assert(varBounds[index] == bound);
        ba[varBounds[index]].setIdx(LABound::BLIdx{index});
    }
    // Post-condition; indices must correspond to the place in the bound list
    assert([&](){
        for (unsigned i = 0; i < varBounds.size_(); ++i) {
            if (ba[varBounds[i]].getIdx().x != i) { return false; }
        }
        return true;
    }());
    return res;
}

void LABoundStore::buildBounds()
{
    for (LVRef v : lvstore) {
        assert(getVarId(v) < bounds.size());
        auto & varBounds = getBounds(v);
        sort<LABoundRef,bound_lessthan>(varBounds, varBounds.size(), bound_lessthan(ba));
        for (unsigned j = 0; j < varBounds.size_(); ++j) {
            ba[varBounds[j]].setIdx(LABound::BLIdx{j});
        }
    }
}
}
