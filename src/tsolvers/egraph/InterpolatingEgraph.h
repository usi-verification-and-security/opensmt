//
// Created by Martin Blicha on 2018-12-15.
//

#ifndef OPENSMT_INTERPOLATINGEGRAPH_H
#define OPENSMT_INTERPOLATINGEGRAPH_H

#include "Egraph.h"
#include "UFInterpolator.h"

#include <api/PartitionManager.h>

namespace opensmt {

class InterpolatingEgraph : public Egraph {
public:
    InterpolatingEgraph(SMTConfig & c, Logic & l) : Egraph{c, l, Egraph::ExplainerType::INTERPOLATING}
    {}


    PTRef getInterpolant(const ipartitions_t& mask, UFInterpolator::ItpColorMap * labels, PartitionManager &pmanager)
    {
        InterpolatingExplainer * itp_explainer = static_cast<InterpolatingExplainer*>(explainer.get());
        auto cgraph = itp_explainer->getCGraph();
        return UFInterpolator(config, logic, *cgraph).getInterpolant(mask, labels, pmanager);
    }
};

}

#endif //OPENSMT_INTERPOLATINGEGRAPH_H
