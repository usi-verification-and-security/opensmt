//
// Created by Martin Blicha on 2018-12-15.
//

#include "InterpolatingEgraph.h"

void InterpolatingEgraph::doExplain(ERef x, ERef y, PtAsgn reason_inequality) {
    // Hook to store interpolation information:
    cgraph_->setConf( getEnode(x).getTerm(), getEnode(y).getTerm(), reason_inequality.tr);
    // Call the original
    Egraph::doExplain(x,y,reason_inequality);
    // cleanup
    delete cgraph;
    cgraph = cgraph_;
    //cgraphs.push(cgraph_);
    cgraph_ = new CGraph(*this, config, logic);
}

void InterpolatingEgraph::explainConstants(ERef p , ERef q) {
    ERef proot = getEnode(p).getRoot();
    ERef qroot = getEnode(q).getRoot();
    cgraph_->setConf( getEnode(proot).getTerm( )
            , getEnode(qroot).getTerm( )
            , PTRef_Undef );
    // Call the original
    Egraph::explainConstants( p, q );
    // cleanup
    delete cgraph;
    cgraph = cgraph_;
    //cgraphs.push(cgraph_);
    cgraph_ = new CGraph(*this, config, logic);
}

void InterpolatingEgraph::expExplainEdge(const ERef v, const ERef p) {
    Egraph::expExplainEdge( v, p);
    const Enode& v_node = getEnode(v);
    const Enode& p_node = getEnode(p);
    assert(v_node.isTerm());
    assert(p_node.isTerm());
    cgraph_->addCNode( v_node.getTerm() );
    cgraph_->addCNode( p_node.getTerm() );
    cgraph_->addCEdge( v_node.getTerm(), p_node.getTerm(), v_node.getExpReason().tr);
}
