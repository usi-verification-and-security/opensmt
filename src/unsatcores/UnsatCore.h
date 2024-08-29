#ifndef OPENSMT_UNSATCORE_H
#define OPENSMT_UNSATCORE_H

#include <minisat/mtl/Vec.h>
#include <pterms/PTRef.h>

namespace opensmt {

class UnsatCore {
public:
    friend class UnsatCoreBuilder;

    vec<PTRef> const & getTerms() const { return terms; }

protected:
    inline UnsatCore(vec<PTRef> && terms_);

    vec<PTRef> terms;
};

UnsatCore::UnsatCore(vec<PTRef> && terms_) : terms{std::move(terms_)} {
    assert(terms.size() > 0);
}

} // namespace opensmt

#endif // OPENSMT_UNSATCORE_H
