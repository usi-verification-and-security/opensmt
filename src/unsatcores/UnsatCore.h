#ifndef OPENSMT_UNSATCORE_H
#define OPENSMT_UNSATCORE_H

#include <minisat/mtl/Vec.h>
#include <pterms/PTRef.h>

#include <iosfwd>

namespace opensmt {

class Logic;
class TermNames;

class UnsatCore {
public:
    virtual ~UnsatCore() = default;

    virtual vec<PTRef> const & getTerms() const = 0;

    void print() const;
    void print(std::ostream &) const;

protected:
    UnsatCore() = default;

    void printBegin(std::ostream &) const;
    void printBody(std::ostream &) const;
    void printEnd(std::ostream &) const;

    virtual void printTerm(std::ostream &, PTRef) const = 0;
};

class NamedUnsatCore : public UnsatCore {
public:
    vec<PTRef> const & getTerms() const override { return namedTerms; }

    vec<PTRef> const & getHiddenTerms() const { return hiddenTerms; }

    std::vector<std::string> makeTermNames() const;
    std::vector<std::string> makeHiddenTermNames() const;

protected:
    friend class UnsatCoreBuilder;

    inline NamedUnsatCore(TermNames const &, vec<PTRef> && namedTerms_, vec<PTRef> && hiddenTerms_);

    void printTerm(std::ostream &, PTRef) const override;

    TermNames const & termNames;

    vec<PTRef> namedTerms;
    vec<PTRef> hiddenTerms;

private:
    std::vector<std::string> makeTermNamesImpl(vec<PTRef> const &) const;
};

class FullUnsatCore : public UnsatCore {
public:
    vec<PTRef> const & getTerms() const override { return terms; }

protected:
    friend class UnsatCoreBuilder;

    inline FullUnsatCore(Logic const &, vec<PTRef> && terms_);

    void printTerm(std::ostream &, PTRef) const override;

    Logic const & logic;

    vec<PTRef> terms;
};

////////////////////////////////////////////////////////////////////////////////

NamedUnsatCore::NamedUnsatCore(TermNames const & termNames_, vec<PTRef> && namedTerms_, vec<PTRef> && hiddenTerms_)
    : termNames{termNames_},
      namedTerms{std::move(namedTerms_)},
      hiddenTerms{std::move(hiddenTerms_)} {
    assert(namedTerms.size() > 0 || hiddenTerms.size() > 0);
}

FullUnsatCore::FullUnsatCore(Logic const & logic_, vec<PTRef> && terms_) : logic{logic_}, terms{std::move(terms_)} {
    assert(terms.size() > 0);
}

} // namespace opensmt

#endif // OPENSMT_UNSATCORE_H
