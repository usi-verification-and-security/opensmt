//
// Created by Martin Blicha on 2018-12-15.
//

#ifndef OPENSMT_INTERPOLATINGEGRAPH_H
#define OPENSMT_INTERPOLATINGEGRAPH_H

#include <PartitionManager.h>
#include "Egraph.h"
#include "UFInterpolator.h"

class InterpolatingEgraph : public Egraph {
public:
    InterpolatingEgraph(SMTConfig & c, Logic & l) : Egraph{c, l}
            , cgraph(nullptr)
            , cgraph_( new CGraph( *this, config, l ) )
    {}

    virtual ~InterpolatingEgraph() override {
        delete cgraph;
        delete cgraph_;
    }

    PTRef getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels, PartitionManager &pmanager)
    {
        return cgraph->getInterpolant(mask, labels, pmanager);
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
