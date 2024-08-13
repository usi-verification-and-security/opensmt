//
// Created by Antti on 18.05.21.
//

#ifndef OPENSMT_KEYVALMAP_H
#define OPENSMT_KEYVALMAP_H

#include "Map.h"

namespace opensmt {

template<class K, class D, class H, class E = Equal<K> >
class MapWithKeys {
    Map<K,D,H,E> map;
    vec<K> keys;
public:
    int getSize() const { return map.getSize(); }
    MapWithKeys () {}
    MapWithKeys (const H& h, const E& e) : map(h, e) {}
    MapWithKeys (MapWithKeys&& o) noexcept : map(std::move(o.map)), keys(std::move(o.keys)) { }

    MapWithKeys&  operator = (MapWithKeys&& o) { std::swap(map, o.map); std::swap(keys, o.keys); return *this; }

    // PRECONDITION: the key must already exist in the map.
    const D& operator [] (const K& k) const
    {
        return map.operator[](k);
    }

    // PRECONDITION: the key must already exist in the map.
    D& operator [] (const K& k)
    {
        return map.operator[](k);
    }

    // PRECONDITION: the key must *NOT* exist in the map.
    void insert (const K& k, const D& d) { map.insert(k, d); keys.push(k); }
    /**
     * Check if k exists in the map.  If it exists, return h[k] i d.  If it does not, d remains unchanged
     * @param k key
     * @param d where to place data
     * @return true if k is in the map and false if k is not in the map.
     */
    bool peek   (const K& k, D& d) const {
        return map.peek(k, d);
    }

    bool has   (const K& k) const {
        return map.has(k);
    }

    const vec<K> & getKeys() const {
        return keys;
    }
    const Map<K,D,H,E> & getMap() const { return map; }

    void copyTo(MapWithKeys & o) const { map.copyTo(o.map); keys.copyTo(o.keys); }

    void clear() { map.clear(); keys.clear(); }
};

}

#endif //OPENSMT_KEYVALMAP_H
