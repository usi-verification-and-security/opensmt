//
// Created by Martin Blicha on 2018-12-15.
//

#ifndef OPENSMT_INTERPOLATINGEGRAPH_H
#define OPENSMT_INTERPOLATINGEGRAPH_H

#include "Egraph.h"
#include "UFInterpolator.h"

class InterpolatingEgraph : public Egraph {
public:
    InterpolatingEgraph(SMTConfig & c , Logic& l
    , vec<DedElem>& d) : Egraph{c,l,d}
            , cgraph_            ( new CGraph( *this, config, l ) )
            , cgraph(nullptr)
    {}

    virtual ~InterpolatingEgraph() override {
        delete cgraph;
        delete cgraph_;
    }

    PTRef getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels)
    {
        return cgraph->getInterpolant(mask, labels);
    }

private:

    CGraph *                cgraph;                   // Holds congrunce graph and compute interpolant
    CGraph *                cgraph_;                   // Holds congrunce graph and compute interpolant

    // overriding base class
    void doExplain(ERef, ERef, PtAsgn) override;
    void explainConstants(ERef, ERef) override;
    void expExplainEdge(ERef, ERef) override;
};

#endif //OPENSMT_INTERPOLATINGEGRAPH_H
