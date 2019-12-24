//
// Created by prova on 21.11.19.
//

#ifndef OPENSMT_SUBSTLOOPBREAKER_H
#define OPENSMT_SUBSTLOOPBREAKER_H
#include <stdint.h>
#include <PTRef.h>
#include <Sort.h>
#include <Alloc.h>
#include <assert.h>
#include <PtStructs.h>
#include <Logic.h>

// For breaking substitution loops
enum class NStatus { inStack, complete, unseen };

template <class T>
struct Ref {
    uint32_t x;
    Ref() : x(INT32_MAX-1) {}
    Ref(uint32_t i) : x(i) {}
    inline friend bool operator== (const Ref& a1, const Ref& a2)   { return a1.x == a2.x; }
    inline friend bool operator!= (const Ref& a1, const Ref& a2)   { return a1.x != a2.x; }
    inline friend bool operator< (const Ref& a1, const Ref& a2)    { return a1.x > a2.x;  }
};


class TVLr {};
typedef Ref<TVLr> TVLRef;
static TVLRef TVLRef_Undef = {INT32_MAX};

class SNr {};
typedef Ref<SNr> SNRef;
static SNRef SNRef_Undef = {INT32_MAX};

class TargetVarList {
    friend class TargetVarListAllocator;

private:
    struct {
        unsigned sz        : 30;
        unsigned proc      : 2; } header;
    union { SNRef s; PTRef t; } vars[0];
    TargetVarList(vec<PTRef>&& _children);
public:
    bool      unprocessed()        const  { return header.proc == 0; }
    bool      processing()         const  { return header.proc == 1; }
    bool      processed()          const  { return header.proc == 2; }
    void      setProcessed()              { header.proc = 2; }
    void      setProcessing()             { header.proc = 1; }
    int       size()               const  { return header.sz; }
    SNRef     operator[]   (int i) const  { assert(i < size()); assert(processed() || processing() ); return vars[i].s; }
    SNRef&    operator[]   (int i)        { assert(i < size()); assert(processed() || processing() ); return vars[i].s; }
    PTRef     getChildTerm (int i) const  { assert(i < size()); assert(unprocessed() || processing() ); return vars[i].t; }
};

class TargetVarListAllocator: RegionAllocator<uint32_t> {
    static int targetVarList32Size(int size) {
        return (sizeof(TargetVarList) + size*sizeof(SNRef))/sizeof(uint32_t);
    }
public:
    TargetVarListAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap) {}
    TargetVarListAllocator() {}

    TVLRef alloc(vec<PTRef>&& _children);

          TargetVarList & operator[](TVLRef r)       { return (TargetVarList&)RegionAllocator<uint32_t>::operator[](r.x); }
    const TargetVarList & operator[](TVLRef r) const { return (TargetVarList&)RegionAllocator<uint32_t>::operator[](r.x); }
private:
    TargetVarList* lea(TVLRef r) { return (TargetVarList*)RegionAllocator<uint32_t>::lea(r.x); }
};



class SubstNode {
    friend class SubstNodeAllocator;
private:
    TargetVarListAllocator& tvla;
    int     procChild;

    int     index;
    int     lowlink;
    NStatus status;
    PTRef   tr;
    SNRef   parent;
    TVLRef  children;

    SubstNode(PTRef tr, PTRef target, TargetVarListAllocator& tvla)
    : tvla(tvla)
    , procChild(0)
    , index(-1)
    , lowlink(-1)
    , status(NStatus::unseen)
    , tr(tr)
    , parent(SNRef_Undef)
    {}

    SubstNode(PTRef tr, PTRef target, vec<PTRef>&& children, TargetVarListAllocator& tvla)
    : SubstNode(tr, target, tvla)
    { this->children = tvla.alloc(std::move(children)); }

    SubstNode(PTRef tr, PTRef target, TVLRef children, TargetVarListAllocator& tvla)
    : SubstNode(tr, target, tvla)
    { this->children = children; }

public:
    PTRef     getTr()            const  { return tr; }
    SNRef     getParent()        const  { return parent; }
    void      setParent(SNRef p)        { parent = p; }
    void      setIndex(int i)           { index = i; }
    int       getIndex()                { return index; }
    void      setLowLink(int i)         { lowlink = i; }
    int       getLowLink()       const  { return lowlink; }
    void      setStatus(NStatus s)      { status = s; }
    NStatus   getStatus()        const  { return status; }
    int       nChildren()        const  { if (children == TVLRef_Undef) return 0; return tvla[children].size(); }

    SNRef&    operator[](int i)         { return tvla[children][i]; }
    SNRef     operator[](int i)  const  { return tvla[children][i]; }
    PTRef     getChildTerm(int i) const { return tvla[children].getChildTerm(i); }

    SNRef     getNextChild();
    void      updateLowLink(int i)      { lowlink = lowlink < i ? lowlink : i; }
    bool      processed()         const { return tvla[children].processed(); }
    bool      processing()        const { return tvla[children].processing(); }
    void      setProcessed()            { tvla[children].setProcessed(); }
    void      setProcessing()           { tvla[children].setProcessing(); }
    bool      hasChildren()       const { return children != TVLRef_Undef; }
    void      swipeChildren()            { children = TVLRef_Undef; }

    void      clearTarjan()             { procChild = 0; index = -1; lowlink = -1; status = NStatus::unseen; }
};

class SubstNodeAllocator : RegionAllocator<uint32_t> {
private:
    static int substNode32Size() {
        return sizeof(SubstNode) / sizeof(uint32_t);
    }
    TargetVarListAllocator& tla;
    const Logic& logic;
    Map<PTRef,TVLRef,PTRefHash> TargetToTargetVarListRef;
    vec<PTRef> getVars(PTRef term) const;
    Map<PTRef,SNRef,PTRefHash> SourceToSNRef;
    vec<SNRef> SNRefs;
public:
    SubstNodeAllocator(TargetVarListAllocator& tla, const Logic& l, uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), tla(tla), logic(l) {}

    SNRef alloc(PTRef tr, PTRef target);

          SubstNode& operator[](SNRef r)       { return (SubstNode&)RegionAllocator<uint32_t>::operator[](r.x); }
    const SubstNode& operator[](SNRef r) const { return (SubstNode&)RegionAllocator<uint32_t>::operator[](r.x); }
    SNRef getSNRefBySource(PTRef ptr)    const { return SourceToSNRef[ptr]; }
    void  clearTarjan();
private:
    SubstNode* lea(SNRef r) { return (SubstNode*)RegionAllocator<uint32_t>::lea(r.x); }

};


class TarjanAlgorithm {
    vec<SNRef> controlStack;
    vec<SNRef> tarjanStack;
    SubstNodeAllocator& sna;
    int index;
    void addNode(SNRef n);
  public:
    TarjanAlgorithm(SubstNodeAllocator &sna) : sna(sna), index(0) {}
    ~TarjanAlgorithm() { sna.clearTarjan(); }
    vec<vec<SNRef>> getLoops(SNRef startNode);
};

class SubstLoopBreaker {
private:

    const Logic& logic;
    Map<PTRef,bool,PTRefHash> seen;
    TargetVarListAllocator tvla;
    SubstNodeAllocator sna;

public:
    SubstLoopBreaker(const Logic& l) : logic(l), tvla(1024), sna(tvla, logic, 1024) {}
    Map<PTRef,PtAsgn,PTRefHash> operator() (Map<PTRef,PtAsgn,PTRefHash>&& substs);
    vec<SNRef> constructSubstitutionGraph(const Map<PTRef,PtAsgn,PTRefHash>& substKeysAndVals);
    vec<vec<SNRef>> findLoops(vec<SNRef>& startNodes);
    vec<SNRef> breakLoops(const vec<vec<SNRef>>& loops);
    std::string printGraphAndLoops(const vec<SNRef>& startNodes, const vec<vec<SNRef>>& loops);
    vec<SNRef> minimizeRoots(vec<SNRef>&& roots) { return std::move(roots); }// nothing here, maybe do some attempt?
    Map<PTRef,PtAsgn,PTRefHash> constructLooplessSubstitution(Map<PTRef,PtAsgn,PTRefHash>&& substs);
};

#endif //OPENSMT_SUBSTLOOPBREAKER_H
