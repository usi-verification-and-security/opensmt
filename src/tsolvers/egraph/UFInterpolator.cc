/*********************************************************************
Author: Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

OpenSMT2 -- Copyright (C) 2008 - 2012 Roberto Bruttomesso

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/


#include "UFInterpolator.h"

#include <logics/Logic.h>
#include <common/InternalException.h>

#include <sys/wait.h>

namespace opensmt {

//#define ITP_DEBUG
//#define COLOR_DEBUG

CNode * CGraph::addCNode(PTRef e) {
    assert (e != PTRef_Undef);
    auto it = cnodes_store.find(e);
    if (it != cnodes_store.end()) { return nullptr; }

    auto n = new CNode(e);
    cnodes_store[e] = n;
    cnodes.push_back(n);
    return n;
}

void CGraph::clear() {
    while (!cnodes.empty()) {
        delete cnodes.back();
        cnodes.pop_back();
    }
    while (!cedges.empty()) {
        delete cedges.back();
        cedges.pop_back();
    }
    cnodes_store.clear();
}

void UFInterpolator::colorNodes() {
    for (auto node : cgraph.getNodes()) {
        colorNode(node);
    }
}

icolor_t UFInterpolator::colorNode(CNode * c) {
    // Already done
    if (colored_nodes.find(c) != colored_nodes.end())
        return c->color;

    icolor_t color = getTermColor(c->e);
    colored_nodes.insert(c);
    assert(color != icolor_t::I_UNDEF);
    return c->color = color;
}

void CGraph::removeCEdge(CEdge * e) {
    if (e == nullptr) return;
    for (std::size_t i = 0; i < cedges.size(); ++i) {
        if (cedges[i] == e) {
            delete e;
            e = nullptr;
            cedges.erase(cedges.begin() + i);
            break;
        }
    }
    assert(e == nullptr);
}

void CGraph::addCEdge(PTRef s, PTRef t, PTRef r) {
    assert(s != t);
    assert (s != PTRef_Undef);
    assert (t != PTRef_Undef);
    // Retrieve corresponding nodes
    CNode * cs = cnodes_store[s];
    CNode * ct = cnodes_store[t];
    addCEdge(cs, ct, r);

}

void CGraph::addCEdge(CNode * from, CNode * to, PTRef reason) {
    auto edge = new CEdge(from, to, reason);
    // Storing edge in cs and ct
    assert (from->edge == nullptr);
    from->edge = edge;
    cedges.push_back(edge);
}

void UFInterpolator::colorCGraph() {
    colorNodes();

    // Edges can be colored as consequence of nodes
    CNode * c1 = cgraph.getConflictStart();
    CNode * c2 = cgraph.getConflictEnd();
    assert(c1 and c2);
    const bool no_mixed = colorEdges(c1, c2);
    if (!no_mixed) throw std::logic_error("Interpolation over mixed literals not supported");
}


bool UFInterpolator::colorEdges(CNode * c1, CNode * c2) {
    std::set<path_t> cache_nodes;
    std::set<CEdge *> cache_edges;
    std::vector<path_t> unprocessed_nodes;
    unprocessed_nodes.emplace_back(c1, c2);
    bool no_mixed = true;
    while (!unprocessed_nodes.empty() && no_mixed) {
        auto node_pair = unprocessed_nodes.back();
        // Skip if path already seen
        if (cache_nodes.find(node_pair) != cache_nodes.end()) {
            unprocessed_nodes.pop_back();
            continue;
        }

        // Push congruence children otherwise
        bool unprocessed_children = false;
        auto processPathFromNode = [&](CNode * x) {
            while (x->edge != nullptr) {
                //
                // Consider only sub-paths with congruence edges
                // Congruence edge is the first time we see
                //
                if (x->edge->reason == PTRef_Undef and cache_edges.insert(x->edge).second) {
                    CNode * n = x->edge->target;
                    assert(logic.getPterm(x->e).size() == logic.getPterm(n->e).size());
                    Pterm const & px = logic.getPterm(x->e);
                    Pterm const & pn = logic.getPterm(n->e);

                    // Iterate over function's arguments
                    for (int i = 0; i < px.size(); ++i) {
                        PTRef arg_x = px[i];
                        PTRef arg_n = pn[i];

                        if (arg_x == arg_n) continue;

                        CNode * arg_n1 = cgraph.getNode(arg_x);
                        CNode * arg_n2 = cgraph.getNode(arg_n);
                        // Push only unprocessed paths
                        path_t next_pair {arg_n1, arg_n2};
                        if (cache_nodes.find(next_pair) == cache_nodes.end()) {
                            unprocessed_nodes.push_back(next_pair);
                            unprocessed_children = true;
                        }
                    }
                }
                x = x->edge->target;
            }
        };
        auto [n1,n2] = node_pair;
        // Direction n1 ----> n2
        processPathFromNode(n1);
        // Direction n1 <--- n2
        processPathFromNode(n2);
        //
        // Color children first
        //
        if (unprocessed_children) { continue; }
        //
        // Otherwise remove this pair
        //
        unprocessed_nodes.pop_back();
        //
        // Color this path
        //
        no_mixed = colorEdgesFrom(n1) && colorEdgesFrom(n2);
        //
        // Remember this path is done
        //
        cache_nodes.insert({n1, n2});
    }
    return no_mixed;
}

//
// It assumes that children have been already colored
// and adjusted
//
bool UFInterpolator::colorEdgesFrom(CNode * x) {
    assert (x);
    // Color from x
    CNode * n = nullptr;
    while (x->edge and x->edge->color == icolor_t::I_UNDEF) {
        n = x->edge->target;
        // Color basic edge with proper color
        if (x->edge->reason != PTRef_Undef) {
            x->edge->color = getLitColor(x->edge->reason);
            assert(x->edge->color != icolor_t::I_AB);
            if (x->edge->color == icolor_t::I_AB) {
                throw InternalException("Error in coloring information");
            }
        } else { // Congruence edge, recurse on arguments
            assert (logic.getPterm(x->e).size() == logic.getPterm(n->e).size());
            // Incompatible colors: this is possible
            // for effect of congruence nodes: adjust
            if ((x->color == icolor_t::I_A && n->color == icolor_t::I_B) || (x->color == icolor_t::I_B && n->color == icolor_t::I_A)) {
                // Need to introduce auxiliary nodes and edges
                // For each argument, find node that is equivalent
                // and of shared color
                vec<PTRef> new_args;
                Pterm const & px = logic.getPterm(x->e);
                Pterm const & pn = logic.getPterm(n->e);

                for (int i = 0; i < pn.size(); ++i) {
                    PTRef arg_x = px[i];
                    PTRef arg_n = pn[i];

                    // If same node, keep
                    if (arg_x == arg_n) {
                        new_args.push(arg_x);
                    } else {
                        CNode * cn_arg_x = cgraph.getNode(arg_x);
                        CNode * cn_arg_n = cgraph.getNode(arg_n);
                        // There is either a path from arg_x to ABcommon
                        // or a path from arg_n to ABcommon (or both)
                        assert(cn_arg_x->edge or cn_arg_n->edge);
                        PTRef abcommon = PTRef_Undef;
                        if (cn_arg_x->color == icolor_t::I_AB) {
                            abcommon = cn_arg_x->e;
                        } else if (cn_arg_n->color == icolor_t::I_AB) {
                            abcommon = cn_arg_n->e;
                        } else { // If argument of x is incompatible with n
                            std::vector<CEdge *> sorted;
                            size_t xnl = getSortedEdges(cn_arg_x, cn_arg_n, sorted);
                            (void) xnl;
                            for (CEdge * edge : sorted) {
                                CNode * from = edge->source;
                                CNode * to = edge->target;
                                assert(from->color != icolor_t::I_UNDEF and to->color != icolor_t::I_UNDEF);
                                if (from->color == icolor_t::I_AB or to->color == icolor_t::I_AB) {
                                    abcommon = from->color == icolor_t::I_AB ? from->e : to->e;
                                    break;
                                }
                            }
                        }
                        assert (abcommon != PTRef_Undef);
                        assert (cgraph.getNode(abcommon)->color == icolor_t::I_AB);
                        new_args.push(abcommon);
                    }
                }

                PTRef nn = logic.mkUninterpFun(logic.getPterm(x->e).symb(), std::move(new_args));
                if (nn == x->e) {
                    x->color = icolor_t::I_AB;
                } else if (nn == n->e) {
                    n->color = icolor_t::I_AB;
                } else {
                    splitEdge(x->edge, nn);
                    x = x->edge->target;
                }
            }
            // Now all the children are colored, we can decide how to color this
            colorCongruenceEdge(x->edge);
        }

        // This edge has been colored
        colored_edges.insert(x->edge);
        assert (x->edge->color == icolor_t::I_A || x->edge->color == icolor_t::I_B);
        // Pass to next node
        x = n;
    }
    // No abmixed if here
    return true;
}

void UFInterpolator::colorCongruenceEdge(CEdge * edge) {
    assert(edge);
    CNode * from = edge->source;
    CNode * to = edge->target;
    if (from->color == to->color) {
        assert (from->color != icolor_t::I_UNDEF);
        edge->color = from->color == icolor_t::I_AB ? resolveABColor() : from->color;
    } else { // Different colors: choose intersection
        // It is not possible that the colors are incompatible
        assert (from->color != icolor_t::I_A or to->color != icolor_t::I_B);
        assert (from->color != icolor_t::I_B or to->color != icolor_t::I_A);
        edge->color = static_cast<icolor_t>(from->color & to->color);
        assert (edge->color == icolor_t::I_A or edge->color == icolor_t::I_B);
    }
}

icolor_t UFInterpolator::determineDisequalityColor(PTRef t1, PTRef t2, ItpColorMap const & conflictColors) const {
    icolor_t conf_color = icolor_t::I_UNDEF;
    PTRef eq = logic.mkEq(t1, t2);
    if (conflictColors.find(eq) != conflictColors.end()) {
        conf_color = conflictColors.at(eq);
        if (conf_color == icolor_t::I_AB) {
            conf_color = resolveABColor();
        }
    } else {
        auto it = std::find_if(conflictColors.begin(), conflictColors.end(), [this](auto const & entry) { return logic.isDisequality(entry.first); });
        if (it != conflictColors.end()) {
            Pterm const & distinctTerm = logic.getPterm(it->first);
            bool t1Present = std::find(distinctTerm.begin(), distinctTerm.end(), t1) != distinctTerm.end();
            bool t2Present = std::find(distinctTerm.begin(), distinctTerm.end(), t2) != distinctTerm.end();
            assert(t1Present and t2Present);
            if (not(t1Present and t2Present)) {
                throw InternalException("Error in UF interpolator, could not determine the color of the conflict equality");
            } else {
                conf_color = it->second;
                if (conf_color == icolor_t::I_AB) {
                    conf_color = resolveABColor();
                }
            }
        } else {
            // equality of two different constants derived
            assert(logic.isConstant(t1) && logic.isConstant(t2));
            if (not(logic.isConstant(t1) && logic.isConstant(t2))) {
                throw InternalException("Error in UF interpolator, could not determine the color of the conflict equality");
            }
            conf_color = resolveABColor();
        }
    }
    assert(conf_color == icolor_t::I_A or conf_color == icolor_t::I_B);
    return conf_color;
}

//
// Here mask is a bit-mask of the form 1..10..0
// which indicates the current splitting for the
// formula into A and B.
//
PTRef
UFInterpolator::getInterpolant(const ipartitions_t & mask, ItpColorMap * labels, PartitionManager & pmanager) {
    assert(labels);
    if (labels) {
        colorInfo = std::make_unique<GlobalTermColorInfo>(pmanager, mask);
        litColors = *labels;
    } else {
        throw InternalException("Error in UFInterpolator::getInterpolant! No labels passed");
    }
    srand(2);
    colorCGraph();

    // Traverse the graph, look for edges of "color" to summarize
    CNode * c1 = cgraph.getConflictStart();
    CNode * c2 = cgraph.getConflictEnd();
    assert(c1);
    assert(c2);
    const path_t pi = path(c1, c2);
    //
    // Compute interpolant as described in Fuchs et al. paper
    // Ground Interpolation for the Theory of Equality
    //
    icolor_t conf_color = determineDisequalityColor(c1->e, c2->e, *labels);
    PTRef result = PTRef_Undef;
    // Conflict belongs to A part
    if (conf_color == icolor_t::I_A) {
        if (usingStrong())
            result = Iprime(pi);
        else if (usingWeak())
            result = logic.mkNot(ISwap(pi));
        else if (usingRandom())
            result = (rand() % 2) ? Iprime(pi) : logic.mkNot(ISwap(pi));
    }
        // Much simpler case when conflict belongs to B
    else if (conf_color == icolor_t::I_B) {
        if (usingStrong())
            result = I(pi);
        else if (usingWeak())
            result = logic.mkNot(IprimeSwap(pi));
        else if (usingRandom())
            result = (rand() % 2) ? I(pi) : logic.mkNot(IprimeSwap(pi));
    } else {
        throw InternalException("something went wrong");
    }

    assert (result != PTRef_Undef);
    return result;
}
//
// Retrieve subpaths. Returns false if the
// entire path belongs to A, which means
// that the interpolant is "false"
//

bool UFInterpolator::getSubpaths(const path_t & pi, path_t & pi_1, path_t & theta, path_t & pi_2) {
    CNode * x = pi.first;
    CNode * y = pi.second;
    assert(x);
    assert(y);
    // Sorted list of edges from x
    std::vector<CEdge *> sorted_edges;
    getSortedEdges(x, y, sorted_edges);

    CNode * lnode = nullptr;
    CNode * rnode = nullptr;

    icolor_t scolor = x->color;
    icolor_t tcolor = y->color;

    if (scolor == icolor_t::I_B || scolor == icolor_t::I_AB) lnode = x;
    else if (tcolor == icolor_t::I_B || tcolor == icolor_t::I_AB) lnode = y;

    if (tcolor == icolor_t::I_B || tcolor == icolor_t::I_AB) rnode = y;
    else if (scolor == icolor_t::I_B || scolor == icolor_t::I_AB) rnode = x;

    if (not lnode or not rnode) {
        for (auto edge : sorted_edges) {
            scolor = edge->source->color;
            tcolor = edge->target->color;

            if (not lnode) {
                if (scolor == icolor_t::I_B || scolor == icolor_t::I_AB) lnode = edge->source;
                else if (tcolor == icolor_t::I_B || tcolor == icolor_t::I_AB) lnode = edge->target;
            }

            if (not rnode) {
                if (tcolor == icolor_t::I_B || tcolor == icolor_t::I_AB) rnode = edge->target;
                else if (scolor == icolor_t::I_B || scolor == icolor_t::I_AB) rnode = edge->source;
            }
        }
    }

    if (not lnode or not rnode or lnode == rnode) {
        //theta empty
        pi_1.first = pi.first;
        pi_1.second = pi.first;
        pi_2.first = pi.first;
        pi_2.second = pi.second;
        return false;
    }

    theta.first = lnode;
    theta.second = rnode;
    pi_1.first = pi.first;
    pi_1.second = theta.first;
    pi_2.first = theta.second;
    pi_2.second = pi.second;
    return true;
}

bool
UFInterpolator::getSubpathsSwap(const path_t & pi, path_t & pi_1, path_t & theta, path_t & pi_2) {
    CNode * x = pi.first;
    CNode * y = pi.second;
    assert(x);
    assert(y);

    // Sorted list of edges from x
    std::vector<CEdge *> sorted_edges;
    getSortedEdges(x, y, sorted_edges);

    CNode * lnode = nullptr;
    CNode * rnode = nullptr;

    icolor_t scolor = x->color;
    icolor_t tcolor = y->color;

    if (scolor == icolor_t::I_A || scolor == icolor_t::I_AB) lnode = x;
    else if (tcolor == icolor_t::I_A || tcolor == icolor_t::I_AB) lnode = y;

    if (tcolor == icolor_t::I_A || tcolor == icolor_t::I_AB) rnode = y;
    else if (scolor == icolor_t::I_A || scolor == icolor_t::I_AB) rnode = x;

    if (not lnode || not rnode) {
        for (auto edge : sorted_edges) {
            scolor = edge->source->color;
            tcolor = edge->target->color;

            if (not lnode) {
                if (scolor == icolor_t::I_A || scolor == icolor_t::I_AB) lnode = edge->source;
                else if (tcolor == icolor_t::I_A || tcolor == icolor_t::I_AB) lnode = edge->target;
            }

            if (not rnode) {
                if (tcolor == icolor_t::I_A || tcolor == icolor_t::I_AB) rnode = edge->target;
                else if (scolor == icolor_t::I_A || scolor == icolor_t::I_AB) rnode = edge->source;
            }
        }
    }

    if (not lnode || not rnode || lnode == rnode) {
        //theta empty
        pi_1.first = pi.first;
        pi_1.second = pi.first;
        pi_2.first = pi.first;
        pi_2.second = pi.second;
        return false;
    }

    theta.first = lnode;
    theta.second = rnode;
    pi_1.first = pi.first;
    pi_1.second = theta.first;
    pi_2.first = theta.second;
    pi_2.second = pi.second;
    return true;
}

PTRef
UFInterpolator::J(const path_t & p, std::vector<path_t> & b_paths) {
    // True on empty path
    if (p.first == p.second) return logic.getTerm_true();

    vec<PTRef> conj;

    for (const auto & path : b_paths) {
        conj.push(logic.mkEq(path.first->e, path.second->e));
    }

    PTRef implicant = logic.mkAnd(conj);
    PTRef implicated = logic.mkEq(p.first->e, p.second->e);

    // Notice that it works also for A-paths like
    //
    // false --> (<= x0 1) --> (<= 2 1)
    //
    // this path says that (<= 2 1) is false, so the implicated
    // should be (not (<= 2 1))

    PTRef res = logic.mkImpl(implicant, implicated);
    return res;
}

PTRef
UFInterpolator::Iprime(const path_t & pi) {
    vec<PTRef> conj;
    // Compute largest subpath of c1 -- c2
    // with B-colorable endpoints
    path_t pi_1, pi_2, theta;
    bool empty_theta = not getSubpaths(pi, pi_1, theta, pi_2);
    // Compute B( pi_1 ) U B( pi_2 )
    std::vector<path_t> b_paths;
    B(pi_1, b_paths);
    B(pi_2, b_paths);

    if (!empty_theta) {
        conj.push(I(theta));
    }

    for (const auto & path : b_paths)
        conj.push(I(path));

    // Finally compute implication
    vec<PTRef> conj_impl;

    for (const auto & path : b_paths)
        conj_impl.push(logic.mkEq(path.first->e, path.second->e));

    PTRef implicant = logic.mkAnd(conj_impl);
    PTRef implicated = PTRef_Undef;

    if (empty_theta)
        implicated = logic.getTerm_false();
    else
        implicated = logic.mkNot(logic.mkEq(theta.first->e, theta.second->e));

    conj.push(logic.mkImpl(implicant, implicated));
    return logic.mkAnd(std::move(conj));
}

PTRef
UFInterpolator::IprimeSwap(const path_t & pi) {
    vec<PTRef> conj;
    // Compute largest subpath of c1 -- c2
    // with B-colorable endpoints
    path_t pi_1, pi_2, theta;
    bool empty_theta = !getSubpathsSwap(pi, pi_1, theta, pi_2);
    // Compute B( pi_1 ) U B( pi_2 )
    std::vector<path_t> b_paths;
    BSwap(pi_1, b_paths);
    BSwap(pi_2, b_paths);

    if (!empty_theta) {
        conj.push(ISwap(theta));
    }

    for (const auto & path : b_paths)
        conj.push(ISwap(path));

    // Finally compute implication
    vec<PTRef> conj_impl;

    for (const auto & path : b_paths) {
        conj_impl.push(logic.mkEq(path.first->e, path.second->e));
    }

    PTRef implicant = logic.mkAnd(conj_impl);
    PTRef implicated = PTRef_Undef;

    if (empty_theta)
        implicated = logic.getTerm_false();
    else
        implicated = logic.mkNot(logic.mkEq(theta.first->e, theta.second->e));

    conj.push(logic.mkImpl(implicant, implicated));
    return logic.mkAnd(std::move(conj));
}

PTRef
UFInterpolator::I(const path_t & p) {
    std::map<path_t, PTRef> cache;
    return Irec(p, cache);
}

PTRef
UFInterpolator::ISwap(const path_t & p) {
    std::map<path_t, PTRef> cache;
    return IrecSwap(p, cache);
}

PTRef
UFInterpolator::Irec(const path_t & p, std::map<path_t, PTRef> & cache) {
    // True on empty path
    if (p.first == p.second) return logic.getTerm_true();

    vec<PTRef> conj;
    vec<PTRef> conj_swap;
    // Will store factors
    std::vector<path_t> factors;
    factors.push_back(p);
    // Will store parents of B-path
    std::vector<path_t> parents;

    const bool a_factor = getFactorsAndParents(p, factors, parents);

    if (factors.size() == 1) {
        // It's an A-path
        if (a_factor) {
            // Compute J
            std::vector<path_t> b_premise_set;
            B(p, b_premise_set);
            conj.push(J(p, b_premise_set));

            for (const auto & fac : b_premise_set) {
                assert (L.find(fac) != L.end());

                if (L[fac] == icolor_t::I_B) {
                    conj.push(Irec(fac, cache));
                } else {
                    //swap here
                    conj_swap.push(logic.mkNot(IprimeSwap(fac)));
                }
            }

            if (conj_swap.size() > 0) {
                conj.push(logic.mkAnd(conj_swap));
            }
        }
            // It's a B-path
        else {
            // Recurse on parents
            for (auto const & parent : parents)
                conj.push(Irec(parent, cache));
        }
    } else {
        // Recurse on factors
        if (factors.size() > 3 && config.itp_euf_alg() > 3) {
            bool la, lb, lab, ra, rb, rab;
            for (std::size_t i = 0; i < factors.size(); i += 3) {
                std::size_t j = i + 2;

                if (j >= factors.size()) j = (factors.size() - 1);

                path_t pf(factors[i].first, factors[j].second);
                CNode * l = pf.first;
                CNode * r = pf.second;

                std::vector<path_t> infactors;
                infactors.push_back(pf);
                std::vector<path_t> inparents;
                const bool a_factor = getFactorsAndParents(pf, infactors, inparents);

                if (j < (factors.size() - 1))
                    assert (infactors.size() >= 3);

                if (infactors.size() >= 2) {
                    if (a_factor) {
                        conj.push(logic.mkNot(IprimeSwap(pf)));
                    } else {
                        conj.push(Irec(pf, cache));
                    }

                    continue;
                }

                la = lb = lab = ra = rb = rab = false;

                if (l->color == icolor_t::I_A) la = true;
                else if (l->color == icolor_t::I_B) lb = true;
                else lab = true;

                if (r->color == icolor_t::I_A) ra = true;
                else if (r->color == icolor_t::I_B) rb = true;
                else rab = true;

                assert (not ((la and rb) or (lb and ra)));
                bool b = true;//rand() % 2;

                if (la or ra) { // conflict in A, call I' or not S
                    assert (i == 0 or j == (factors.size() - 1));

                    if (b and config.itp_euf_alg() == 4) {
                        conj.push(Irec(pf, cache));
                    } else {
                        conj.push(logic.mkNot(IprimeSwap(pf)));
                    }
                } else if (lb or rb) { // conflict in B, call I or not S'
                    assert (i == 0 or j == (factors.size() - 1));

                    if (b and config.itp_euf_alg() == 4) {
                        conj.push(Irec(pf, cache));
                    } else {
                        conj.push(logic.mkNot(IprimeSwap(pf)));
                    }
                } else { // conflict has global endpoints
                    if (b and config.itp_euf_alg() == 4) {
                        conj.push(Irec(pf, cache));
                    } else {
                        conj.push(logic.mkNot(IprimeSwap(pf)));
                    }
                }
            }
        } else {
            for (const auto & factor : factors)
                conj.push(Irec(factor, cache));
        }
    }

    PTRef res = logic.mkAnd(std::move(conj));
    assert (res != PTRef_Undef);
    return res;
}

PTRef
UFInterpolator::IrecSwap(const path_t & p, std::map<path_t, PTRef> & cache) {
    // True on empty path
    if (p.first == p.second) return logic.getTerm_true();

    vec<PTRef> conj;
    vec<PTRef> conj_swap;
    // Will store factors
    std::vector<path_t> factors;
    factors.push_back(p);
    // Will store parents of A-path
    std::vector<path_t> parents;

    const bool a_factor = getFactorsAndParents(p, factors, parents);

    if (factors.size() == 1) {
        // It's a B-path
        if (!a_factor) {
            // Compute J
            std::vector<path_t> b_premise_set;
            BSwap(p, b_premise_set);
            conj.push(J(p, b_premise_set));
            for (const auto & fac : b_premise_set) {
                assert (L.find(fac) != L.end());

                if (L[fac] == icolor_t::I_A) {
                    conj.push(IrecSwap(fac, cache));
                } else {
                    conj_swap.push(logic.mkNot(Iprime(fac)));
                }
            }

            if (conj_swap.size() > 0) {
                conj.push(logic.mkAnd(conj_swap));
            }
        } else { // It's an A-path

            // Recurse on parents
            for (const auto & parent : parents) {
                conj.push(IrecSwap(parent, cache));
            }
        }
    } else {
        // Recurse on factors
        if (factors.size() > 3 and config.itp_euf_alg() > 3) {
            bool la, lb, lab, ra, rb, rab;
            for (std::size_t i = 0; i < factors.size(); i += 3) {
                std::size_t j = i + 2;

                if (j >= factors.size()) j = (factors.size() - 1);

                path_t pf(factors[i].first, factors[j].second);
                CNode * l = pf.first;
                CNode * r = pf.second;

                std::vector<path_t> infactors;
                infactors.push_back(pf);
                std::vector<path_t> inparents;
                const bool a_factor = getFactorsAndParents(pf, infactors, inparents);

                if (j < (factors.size() - 1))
                    assert (infactors.size() >= 3);

                if (infactors.size() >= 2) {
                    if (!a_factor)
                        conj.push(logic.mkNot(Iprime(pf)));
                    else
                        conj.push(IrecSwap(pf, cache));

                    continue;
                }
                la = lb = lab = ra = rb = rab = false;

                if (l->color == icolor_t::I_A) la = true;
                else if (l->color == icolor_t::I_B) lb = true;
                else lab = true;

                if (r->color == icolor_t::I_A) ra = true;
                else if (r->color == icolor_t::I_B) rb = true;
                else rab = true;

                assert (not ((la and rb) or (lb and ra)));
                bool b = true;//rand() % 2;

                if (la or ra) {
                    assert (i == 0 or j == (factors.size() - 1));

                    if (b and config.itp_euf_alg() == 4) {
                        conj.push(logic.mkNot(Iprime(pf)));
                    } else {
                        conj.push(IrecSwap(pf, cache));
                    }
                } else if (lb or rb) {
                    assert (i == 0 or j == (factors.size() - 1));

                    if (b and config.itp_euf_alg() == 4) {
                        conj.push(logic.mkNot(Iprime(pf)));
                    } else {
                        conj.push(IrecSwap(pf, cache));
                    }
                } else { // conflict has global endpoints
                    if (b and config.itp_euf_alg() == 4) {
                        conj.push(logic.mkNot(Iprime(pf)));
                    } else {
                        conj.push(IrecSwap(pf, cache));
                    }
                }
            }
        } else {
            for (const auto & factor : factors) {
                conj.push(IrecSwap(factor, cache));
            }
        }
    }

    PTRef res = logic.mkAnd(std::move(conj));
    assert (res != PTRef_Undef);
    return res;
}

void UFInterpolator::B(const path_t & p, std::vector<path_t> & b_premise_set) {
    std::set<path_t> cache;
    Brec(p, b_premise_set, cache);
}

void UFInterpolator::BSwap(const path_t & p, std::vector<path_t> & a_premise_set) {
    std::set<path_t> cache;
    BrecSwap(p, a_premise_set, cache);
}

void UFInterpolator::Brec(const path_t & p, std::vector<path_t> & b_premise_set, std::set<path_t> & cache) {
    // Skip trivial call
    if (p.first == p.second) return;

    // Skip seen calls
    if (!cache.insert(p).second) return;

    // Will store factors
    std::vector<path_t> factors;
    factors.push_back(p);
    // Will store parents of B-path
    std::vector<path_t> parents;

    const bool a_factor = getFactorsAndParents(p, factors, parents);

    if (factors.size() == 1) {
        // It's an A-path
        if (a_factor) {
            for (const auto & parent : parents)
                Brec(parent, b_premise_set, cache);
        } else { // It's a B-path
            b_premise_set.push_back(p);
        }
    } else {
        // Recurse on factors
        for (const auto & factor : factors)
            Brec(factor, b_premise_set, cache);
    }
}

void UFInterpolator::BrecSwap(const path_t & p, std::vector<path_t> & a_premise_set, std::set<path_t> & cache) {
    // Skip trivial call
    if (p.first == p.second) return;

    // Skip seen calls
    if (!cache.insert(p).second) return;

    // Will store factors
    std::vector<path_t> factors;
    factors.push_back(p);
    // Will store parents of B-path
    std::vector<path_t> parents;

    const bool a_factor = getFactorsAndParents(p, factors, parents);

    if (factors.size() == 1) {
        // It's an A-path
        if (not a_factor) {
            for (const auto & parent : parents)
                BrecSwap(parent, a_premise_set, cache);
        } else { // It's a B-path
            a_premise_set.push_back(p);
        }
    } else {
        // Recurse on factors
        for (const auto & factor : factors)
            BrecSwap(factor, a_premise_set, cache);
    }
}

//
// We don't know how to reach x from y. There are
// three cases to consider (see below). This procedure
// retrieves the edges in the correct order to reach
// y from x
//
size_t UFInterpolator::getSortedEdges(CNode * x, CNode * y, std::vector<CEdge *> & sorted_edges) {
    assert (x);
    assert (y);
    assert (x != y);

    CNode * x_orig = x;
    CNode * y_orig = y;

    std::set<CNode *> visited;
    visited.insert(x);
    visited.insert(y);

    std::vector<CEdge *> & from_x = sorted_edges;
    std::vector<CEdge *> tmp;

    bool done = false;

    while (not done) {
        // Advance x by 1
        if (x->edge != nullptr) {
            CEdge * candidate = x->edge;
            x = x->edge->target;

            // Touching an already seen node (by y)
            // x is the nearest common ancestor
            // Clear y vector until x is found
            if (not visited.insert(x).second) {
                while (not tmp.empty() and tmp.back()->target != x) {
                    tmp.pop_back();
                }
                done = true;
            }

            from_x.push_back(candidate);
        }

        if (done) break;

        // Advance y by 1
        if (y->edge) {
            CEdge * candidate = y->edge;
            y = y->edge->target;
            // Touching an already seen node (by x)
            // y is the nearest common ancestor
            // Clear x vector until y is found
            if (not visited.insert(y).second) {
                while (not from_x.empty() && from_x.back()->target != y) {
                    from_x.pop_back();
                }
                done = true;
            }
            tmp.push_back(candidate);
        }
    }
    x = x_orig;
    y = y_orig;

    const size_t x_path_length = sorted_edges.size();

    // The two paths must collide
    assert (not tmp.empty() or sorted_edges.back()->target == y);
    assert (not sorted_edges.empty() or tmp.back()->target == x);
    assert (sorted_edges.empty()
            or tmp.empty()
            or sorted_edges.back()->target == tmp.back()->target);

    // Now load edges from y in the correct order
    while (not tmp.empty()) {
        sorted_edges.push_back(tmp.back());
        tmp.pop_back();
    }

    return x_path_length;
}

icolor_t UFInterpolator::resolveABColor() const {
    if (usingStrong()) {
        return icolor_t::I_B;
    } else if (usingWeak()) {
        return icolor_t::I_A;
    } else if (usingRandom()) {
        return (rand() % 2) ? icolor_t::I_A : icolor_t::I_B;
    } else {
        assert(false);
        return icolor_t::I_B;
    }
}

//
// Return the set of factors
bool UFInterpolator::getFactorsAndParents(const path_t & p, std::vector<path_t> & factors, std::vector<path_t> & parents) {
    assert (factors.size() == 1);
    assert (parents.empty());
    CNode * x = p.first;
    CNode * y = p.second;
    assert (x);
    assert (y);
    std::vector<CEdge *> sorted_edges;
    const size_t x_path_length = getSortedEdges(x, y, sorted_edges);

    const bool a_factor = sorted_edges[0]->color == icolor_t::I_A;
    icolor_t last_color = sorted_edges[0]->color;
    x = 0 < x_path_length
        ? sorted_edges[0]->target
        : sorted_edges[0]->source;
    y = p.second;
    size_t i = 1;

    // Add parents
    if (sorted_edges[0]->reason == PTRef_Undef) {
        CNode * tx = p.first;
        CNode * tn = x;
        assert (logic.getPterm(tx->e).size() == logic.getPterm(tn->e).size());
        // Examine children of the congruence edge
        Pterm const & px = logic.getPterm(tx->e);
        Pterm const & pn = logic.getPterm(tn->e);

        for (int j = 0; j < px.size(); ++j) {
            PTRef arg_tx = px[j];
            PTRef arg_tn = pn[j];

            if (arg_tn == arg_tx) continue;

            // Add parents for further recursion
            parents.push_back(path(cgraph.getNode(arg_tx), cgraph.getNode(arg_tn)));
        }
    }
    CNode * n;
    while (x != y) {
        // Next x
        n = i < x_path_length
            ? sorted_edges[i]->target
            : sorted_edges[i]->source;

        // Retrieve parents for congruence edges
        if (sorted_edges[i]->reason == PTRef_Undef) {
            assert (logic.getPterm(x->e).size() == logic.getPterm(n->e).size());
            // Examine children of the congruence edge
            Pterm const & px = logic.getPterm(x->e);
            Pterm const & pn = logic.getPterm(n->e);

            for (int j = 0; j < px.size(); ++j) {
                PTRef arg_x = px[j];
                PTRef arg_n = pn[j];

                if (arg_n == arg_x) continue;

                // Add parents for further recursion
                parents.push_back(path(cgraph.getNode(arg_x), cgraph.getNode(arg_n)));
            }
        }

        // New factor
        if (i < sorted_edges.size() and sorted_edges[i]->color != last_color) {
            factors.back().second = x;
            factors.push_back(path(x, y));
            last_color = sorted_edges[i]->color;
        }
        i++;
        x = n;
    }

    labelFactors(factors);

    return a_factor;
}

void
UFInterpolator::labelFactors(std::vector<path_t> & factors) {
    // McMillan
    if (usingStrong())
        for (const auto & factor : factors)
            L[factor] = icolor_t::I_B;

    // McMillan'
    else if (usingWeak())
        for (const auto & factor : factors)
            L[factor] = icolor_t::I_A;

    // Random
    else if (usingRandom()) {
        for (const auto & factor : factors) {
            if (rand() % 2) {
                L[factor] = icolor_t::I_B;
            } else {
                L[factor] = icolor_t::I_A;
            }
        }
    }
}

void UFInterpolator::printAsDotty(std::ostream & os) {
    os << "digraph cgraph {" << '\n';

    // Print all nodes
    for (CNode * c : cgraph.getNodes()) {
        std::string color = "grey";

        if (c->color == icolor_t::I_A) color = "red";

        if (c->color == icolor_t::I_B) color = "blue";

        if (c->color == icolor_t::I_AB) color = "green";

        os << logic.getPterm(c->e).getId().x
           << " [label=\""
           << logic.pp(c->e)
           << "\",color=\"" << color
           << "\",style=filled]"
           << '\n';
    }

    // Print all edges
    for (CEdge * c : cgraph.getEdges()) {
        std::string color = "grey";

        if (c->color == icolor_t::I_A) color = "red";

        if (c->color == icolor_t::I_B) color = "blue";

        if (c->color == icolor_t::I_AB) color = "green";

        os << logic.getPterm(c->source->e).getId().x
           << " -> "
           << logic.getPterm(c->target->e).getId().x
           << " [color=\"" << color
           << "\",style=\"bold"
           << (c->reason == PTRef_Undef ? ",dashed" : "")
           << "\"]"
           << '\n';
    }

    // Print conflict
    os << logic.pp(cgraph.getConflictStart()->e)
       << " -> "
       << logic.pp(cgraph.getConflictEnd()->e)
       << " [style=bold]"
       << '\n';
    os << "}" << '\n';
}

bool UFInterpolator::checkColors() const {
    for (CEdge * edge : cgraph.getEdges()) {
        // Edge that is not involved
        if (edge->color == icolor_t::I_UNDEF)
            continue;

        // Check color is A or B
        if (edge->color != icolor_t::I_A and edge->color != icolor_t::I_B)
            return false;

        // Check color is consistent with nodes
        if ((edge->color & edge->source->color) == icolor_t::I_UNDEF
            || (edge->color & edge->target->color) == icolor_t::I_UNDEF) {
            return false;
        }
    }
    return true;
}

void UFInterpolator::splitEdge(CEdge * edge, PTRef intermediateTerm) {
    assert(edge);
    CNode * from = edge->source;
    CNode * to = edge->target;
    assert (from->edge->target == to);
    // Adds corresponding node
    CNode * intermediate = nullptr;
    CNode * intermediate_next = nullptr;
    PTRef intermediate_next_reason = PTRef_Undef;
    if (cgraph.hasNode(intermediateTerm)) {
        intermediate = cgraph.getNode(intermediateTerm);
        if (intermediate->edge) {
            intermediate_next = intermediate->edge->target;
            intermediate_next_reason = intermediate->edge->reason;
            cgraph.removeCEdge(intermediate->edge);
        }
        intermediate->edge = nullptr;
    } else {
        intermediate = cgraph.addCNode(intermediateTerm);
    }
    intermediate->color = icolor_t::I_AB;
    // We have the intermediate node in hand, now we need to remove edge "from -> to" and
    // add edges "from -> intermediate"; "intermediate -> to"
    cgraph.removeCEdge(edge);
    from->edge = nullptr;
    cgraph.addCEdge(from, intermediate, PTRef_Undef);
    assert(from->edge != nullptr); // the added edge is from->next
    assert(from->edge->target == intermediate);
    // Choose a color; we know that intermediate is AB, so we color edge based on from
    assert (from->color == icolor_t::I_A || from->color == icolor_t::I_B || from->color == icolor_t::I_AB);
    from->edge->color = from->color == icolor_t::I_AB ? resolveABColor() : from->color;

    cgraph.addCEdge(intermediate, to, PTRef_Undef);
    if (intermediate_next) {
        // MB: There are two special cases: when `intermediate_next` was `to` and when it was `from`
        if (intermediate_next == to) {
            // In this case a new edge from `to` to `intermediate_next` would be a self-loop
            // We simple do not add it, but use the original reason
            intermediate->edge->reason = intermediate_next_reason;
        } else if (intermediate_next == from) {
            // In this case a new edge from `to` to `intermediate_next` would form a triangular loop
            // `from` -> `intermediate` -> `to` -> `from`
            // We do not add the edge, but update the reason for edge `from` -> `intermediate`
            assert(from->edge->reason == PTRef_Undef);
            from->edge->reason = intermediate_next_reason;
        } else {
            cgraph.addCEdge(to, intermediate_next, intermediate_next_reason);
        }
    }
}

}
