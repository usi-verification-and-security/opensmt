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
    InterpolatingEgraph(SMTConfig & c, Logic & l) : Egraph{c, l, Egraph::ExplainerType::INTERPOLATING}
    {}


    PTRef getInterpolant(const ipartitions_t& mask, map<PTRef, icolor_t> *labels, PartitionManager &pmanager)
    {
        InterpolatingExplainer * itp_explainer = static_cast<InterpolatingExplainer*>(explainer.get());
        auto cgraph = itp_explainer->getCGraph();
        return UFInterpolator(config, logic, *cgraph).getInterpolant(mask, labels);
    }
};

#endif //OPENSMT_INTERPOLATINGEGRAPH_H
