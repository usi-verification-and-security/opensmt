#ifndef OPENSMT_UNSATCORE_H
#define OPENSMT_UNSATCORE_H

#include <minisat/mtl/Vec.h>
#include <pterms/PTRef.h>

namespace opensmt {

class UnsatCore {
public:
    friend class UnsatCoreBuilder;

    vec<PTRef> const & getTerms() const { return terms; }
    vec<PTRef> const & getNamedTerms() const { return namedTerms; }

protected:
    inline UnsatCore(vec<PTRef> && terms_, vec<PTRef> && namedTerms_);

    vec<PTRef> terms;
    vec<PTRef> namedTerms;
};

UnsatCore::UnsatCore(vec<PTRef> && terms_, vec<PTRef> && namedTerms_)
    : terms{std::move(terms_)},
      namedTerms{std::move(namedTerms_)} {
    assert(terms.size() > 0);
}

} // namespace opensmt

#endif // OPENSMT_UNSATCORE_H
