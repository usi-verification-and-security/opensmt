#ifndef OPENSMT_USERTERMMAP_H
#define OPENSMT_USERTERMMAP_H

#include <pterms/PTRef.h>

#include <unordered_map>

namespace opensmt {
class InternalToUserTermMap {
public:
    bool maybeAddMapping(PTRef newTerm, PTRef userTerm) {
        if (newTerm == userTerm) { return false; }

        // overwrite any previous mappings
        map.insert_or_assign(newTerm, userTerm);
        return true;
    }

    PTRef getUserTerm(PTRef term) const {
        auto it = map.find(term);
        if (it == map.end()) { return term; }

        assert(it->first.x == term.x);
        return it->second;
    }

private:
    std::unordered_map<PTRef, PTRef, PTRefHash> map;
};
} // namespace opensmt

#endif // OPENSMT_USERTERMMAP_H
