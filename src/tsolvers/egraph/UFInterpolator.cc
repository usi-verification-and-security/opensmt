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


#include <sys/wait.h>
#include "UFInterpolator.h"
#include "Logic.h"

//#define ITP_DEBUG
//#define COLOR_DEBUG

void CGraph::addCNode(PTRef e) {
    assert (e != PTRef_Undef);
    auto it = cnodes_store.find(e);
    if (it != cnodes_store.end()) { return; }

    CNode * n = new CNode(e);
    cnodes_store[e] = n;
    cnodes.push_back(n);
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
    assert(color != I_UNDEF);
    return c->color = color;
}

void
CGraph::removeCEdge(CEdge * e) {
    if (e == nullptr) return;
    for (std::size_t i = 0; i < cedges.size(); ++i) {
        if (cedges[i] == e) {
            cedges.erase(cedges.begin() + i);
            break;
        }
    }
}

void CGraph::addCEdge(PTRef s, PTRef t, PTRef r) {
    assert(s != t);
    assert (s != PTRef_Undef);
    assert (t != PTRef_Undef);
    // Retrieve corresponding nodes
    CNode * cs = cnodes_store[s];
    CNode * ct = cnodes_store[t];
    // Create edge
    CEdge * edge = new CEdge(cs, ct, r);
    // Storing edge in cs and ct
    assert (cs->next == nullptr);
    cs->next = edge;
    ct->prev.insert(edge);
    cedges.push_back(edge);
}

void UFInterpolator::colorCGraph() {
    colorNodes();

    // Uncomment to print
    // ofstream nout( "nodecol_graph.dot" );
    // printAsDotty( nout );
    // cerr << "[Dumped nodecol_graph.dot]" << endl;

    // Edges can be colored as consequence of nodes
    CNode * c1 = cgraph.getConflictStart();
    CNode * c2 = cgraph.getConflictEnd();
    assert(c1 and c2);
    const bool no_mixed = colorEdges(c1, c2);
    if (!no_mixed) throw std::logic_error("Interpolation over mixed literals not supported");
}


bool UFInterpolator::colorEdges(CNode * c1, CNode * c2) {
    std::set<std::pair<CNode *, CNode *>> cache_nodes;
    std::set<CEdge *> cache_edges;
    std::vector<CNode *> unprocessed_nodes;
    unprocessed_nodes.push_back(c1);
    unprocessed_nodes.push_back(c2);
    bool no_mixed = true;
    while (!unprocessed_nodes.empty() && no_mixed) {
        assert (unprocessed_nodes.size() % 2 == 0);
        CNode * n1 = unprocessed_nodes[unprocessed_nodes.size() - 2];
        CNode * n2 = unprocessed_nodes[unprocessed_nodes.size() - 1];
        //
        // Skip if path already seen
        //
        if (cache_nodes.find(std::make_pair(n1, n2)) != cache_nodes.end()) {
            unprocessed_nodes.pop_back();
            unprocessed_nodes.pop_back();
            continue;
        }
        //
        // Push congruence children otherwise
        //
        bool unprocessed_children = false;
        auto processPathFromNode = [&](CNode * x) {
            while (x->next != nullptr) {
                //
                // Consider only sub-paths with congruence edges
                // Congruence edge is the first time we see
                //
                if (x->next->reason == PTRef_Undef && cache_edges.insert(x->next).second) {
                    CNode * n = x->next->target;
                    assert (logic.getPterm(x->e).size() == logic.getPterm(n->e).size());
                    // getArity = pterm->size
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
                        if (cache_nodes.find(std::make_pair(arg_n1, arg_n2)) == cache_nodes.end()) {
                            unprocessed_nodes.push_back(arg_n1);
                            unprocessed_nodes.push_back(arg_n2);
                            unprocessed_children = true;
                        }
                    }
                }
                x = x->next->target;
            }
        };
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
        unprocessed_nodes.pop_back();
        //
        // Color this path
        //
        no_mixed = colorEdgesFrom(n1) && colorEdgesFrom(n2);
        //
        // Remember this path is done
        //
        cache_nodes.insert(std::make_pair(n1, n2));
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
    while (x->next != nullptr && x->next->color == I_UNDEF) {
        n = x->next->target;
        // Congruence edge, recurse on arguments
        if (x->next->reason == PTRef_Undef) {
            assert (logic.getPterm(x->e).size() == logic.getPterm(n->e).size());
            // Incompatible colors: this is possible
            // for effect of congruence nodes: adjust
            if ((x->color == I_A && n->color == I_B) || (x->color == I_B && n->color == I_A)) {
                vec<PTRef> eadj;
                eadj.push(x->e);
                eadj.push(n->e);
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
                        assert(cn_arg_x->next != nullptr || cn_arg_n->next != nullptr);
                        PTRef abcommon = PTRef_Undef;
                        if (cn_arg_x->color == I_AB) {
                            abcommon = cn_arg_x->e;
                        } else if (cn_arg_n->color == I_AB) {
                            abcommon = cn_arg_n->e;
                        }
                            // If argument of x is incompatible with n
                        else {
                            //cerr << "; Edges from X to N" << endl;
                            std::vector<CEdge *> sorted;
                            size_t xnl = getSortedEdges(cn_arg_x, cn_arg_n, sorted);
                            (void) xnl;
                            for (CEdge * edge : sorted) {
                                CNode * from = edge->source;
                                CNode * to = edge->target;
                                assert(from->color != I_UNDEF and to->color != I_UNDEF);
                                if (from->color == I_AB || to->color == I_AB) {
                                    abcommon = from->color == I_AB ? from->e : to->e;
                                    break;
                                }
                            }
                        }
                        assert (abcommon != PTRef_Undef);
                        //cerr << "; Node " << logic.printTerm(abcommon) << " is AB" << endl;
                        assert (cgraph.getNode(abcommon)->color == I_AB);
                        new_args.push(abcommon);
                    }
                }

                PTRef nn = logic.mkUninterpFun(logic.getPterm(x->e).symb(), new_args);
                assert (nn != x->e);
                assert (nn != n->e);
                // Adds corresponding node
                CNode * cnn = nullptr;
                CNode * cnn_next = nullptr;
                PTRef cnn_next_reason = PTRef_Undef;
                if (cgraph.hasNode(nn)) {
                    cnn = cgraph.getNode(nn);
                    if (cnn->next != nullptr) {
                        cnn_next = cnn->next->target;
                        cnn_next_reason = cnn->next->reason;
                        cgraph.removeCEdge(cnn->next);
                    }
                    cnn->next = nullptr;
                } else {
                    cgraph.addCNode(nn);
                    cnn = cgraph.getNode(nn);
                }
                // Remember this
                assert (x->next->target == n);
                cnn->color = I_AB;

                // Situation x --> n | then make x --> nn
                cgraph.removeCEdge(x->next);
                x->next = nullptr;
                cgraph.addCEdge(x->e, nn, PTRef_Undef);
                assert(x->next != nullptr); // the added edge is x->next
                assert(x->next->target == cnn);
                // Choose a color
                assert (x->color == I_A || x->color == I_B || x->color == I_AB);
                x->next->color = x->color == I_AB ? resolveABColor() : x->color;

                cgraph.addCEdge(nn, n->e, PTRef_Undef);
                cnn->next->color = n->color;
                x = cnn;
                if (cnn_next != nullptr) {
                    // MB: It looks like it is possible that there has already been an edge n -> cnn
                    // In that case a self-loop edge would be added here and that causes trouble later
                    // We need to prevent that
                    if (cnn_next == n) {
                        cnn->next->reason = cnn_next_reason;
                    } else {
                        cgraph.addCEdge(n->e, cnn_next->e, cnn_next_reason);
                    }
                }
            }
            // Now all the children are colored, we can decide how to color this
            if (x->color == n->color) {
                assert (x->color);
                // Choose correct color
                x->next->color = x->color == I_AB ? resolveABColor() : x->color;
            }
                // Different colors: choose intersection
            else {
                // It is not possible that are incompatible
                assert (x->color != I_A || n->color != I_B);
                assert (x->color != I_B || n->color != I_A);
                x->next->color = static_cast< icolor_t > ( x->color & n->color );
                assert (x->next->color == I_A
                        || x->next->color == I_B);
            }
        }
            // Color basic edge with proper color
        else {
            x->next->color = getLitColor(x->next->reason);
            assert(x->next->color != I_AB);
            if (x->next->color == I_AB) {
                throw std::logic_error("Error in coloring information");
            }
        }

        // This edge has been colored
        colored_edges.insert(x->next);
        assert (x->next->color == I_A || x->next->color == I_B);
        // Pass to next node
        x = n;
    }
    // No abmixed if here
    return true;
}

//
// Here mask is a bit-mask of the form 1..10..0
// which indicates the current splitting for the
// formula into A and B.
//
PTRef
UFInterpolator::getInterpolant(const ipartitions_t & mask, std::map<PTRef, icolor_t> * labels) {
    assert(labels);
    (void)mask;
    srand(2);
    computeAndStoreColors(*labels);
    colorCGraph();

    // Uncomment to print
    // static int count = 1;
    // char buf[ 32 ];
    // sprintf( buf, "graph_%d.dot", count ++ );
    // ofstream out( buf );
    // printAsDotty( out );
    // cerr << "[Dumped " << buf << "]" << endl;

    // Traverse the graph, look for edges of "color" to summarize
    CNode * c1 = cgraph.getConflictStart();
    CNode * c2 = cgraph.getConflictEnd();

    assert (c1);
    assert (c2);
    icolor_t conf_color = I_UNDEF;
    PTRef eq = logic.mkEq(c1->e, c2->e);

    if (labels != nullptr && (labels->find(eq) != labels->end())) {
        conf_color = (*labels)[eq];
        if (conf_color == I_AB) {
            conf_color = resolveABColor();
        }
    } else {
        // equality of two different constants derived
        assert(logic.isConstant(c1->e) && logic.isConstant(c2->e));
        if (not(logic.isConstant(c1->e) && logic.isConstant(c2->e))) {
            throw std::logic_error("Error in UF interpolator, could not determine the color of the conflict equality");
        }
        conf_color = resolveABColor();
    }
    assert (conf_color == I_A || conf_color == I_B);

    PTRef result = PTRef_Undef;
    path_t pi = path(c1, c2);

    //
    // Compute interpolant as described in Fuchs et al. paper
    // Ground Interpolation for the Theory of Equality
    //
    // Conflict belongs to A part
    if (conf_color == I_A) {
//      cerr << "; Conflict in A" << endl;
        if (usingStrong())
            result = Iprime(pi);
        else if (usingWeak())
            result = logic.mkNot(ISwap(pi));
        else if (usingRandom())
            result = (rand() % 2) ? Iprime(pi) : logic.mkNot(ISwap(pi));
    }
        // Much simpler case when conflict belongs to B
    else if (conf_color == I_B) {
        //    cerr << "; Conflict in B" << endl;
        if (usingStrong())
            result = I(pi);
        else if (usingWeak())
            result = logic.mkNot(IprimeSwap(pi));
        else if (usingRandom())
            result = (rand() % 2) ? I(pi) : logic.mkNot(IprimeSwap(pi));
    } else {
        opensmt_error ("something went wrong");
    }

    assert (result != PTRef_Undef);
    return result;
}

void UFInterpolator::computeAndStoreColors(const map<PTRef, icolor_t> & literalColors) {
    // MB: NOTE! If P(a) is A-local, but both symbols P and a are shared, than P(a) should be shared and not A-local
    using entry_t = std::pair<const PTRef, icolor_t>;
    std::vector<entry_t> queue;
    for (auto entry : literalColors) {
        queue.push_back(entry);
        this->litColors.insert(entry);
    }
    std::unordered_map<SymRef, icolor_t, SymRefHash> symbolColors;
    while (not queue.empty()) {
        auto const & entry = queue.back();
        icolor_t colorToAssign = entry.second;
        PTRef term = entry.first;
        queue.pop_back();
        auto it = termColors.find(term);
        if (it != termColors.end()) {
            icolor_t assignedColor = it->second;
            if (assignedColor == colorToAssign || assignedColor == I_AB) { // already processed, color does not change
                continue;
            } else { // assigning new color
                assert(assignedColor == I_A or assignedColor == I_B);
                colorToAssign = static_cast<opensmt::icolor_t>(colorToAssign | assignedColor);
                assert(colorToAssign == I_AB);
            }
        }
        // if we reach here, we need to propagate colorToAssign to children
        termColors[term] = colorToAssign;
        for (int i = 0; i < logic.getPterm(term).size(); ++i) {
            PTRef child = logic.getPterm(term)[i];
            queue.emplace_back(child, colorToAssign);
        }
        // add symbol information
        auto insertRes = symbolColors.insert(std::make_pair(logic.getSymRef(term), colorToAssign));
        if (not insertRes.second) { // there was entry for this symbol already
            auto entryIt = insertRes.first;
            entryIt->second = static_cast<opensmt::icolor_t>(entryIt->second | colorToAssign);
        }
    }
    // Make sure complex terms have correct color assigned
    for (auto & entry : termColors) {
        PTRef term = entry.first;
        auto color = entry.second;
        if (color != I_AB and (logic.isUF(term) or logic.isUP(term))) {
            // if symbol is AB and all children are AB, this term should also be AB
            auto symbolColor = symbolColors.at(logic.getSymRef(term));
            if (symbolColor != I_AB) { continue; }
            for (int i = 0; i < logic.getPterm(term).size(); ++i) {
                PTRef child = logic.getPterm(term)[i];
                if (termColors.at(child) != I_AB) { continue; }
            }
            // everything is AB -> update
            entry.second = I_AB;
        }
    }
    // Make sure true and false have color
    termColors[logic.getTerm_true()] = I_AB;
    termColors[logic.getTerm_false()] = I_AB;
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
//    cerr << "; Computing subpaths" << endl;
    // Sorted list of edges from x
    vector<CEdge *> sorted_edges;
    getSortedEdges(x, y, sorted_edges);

    CNode * lnode = nullptr;
    CNode * rnode = nullptr;

    icolor_t scolor = x->color;
    icolor_t tcolor = y->color;

    if (scolor == I_B || scolor == I_AB) lnode = x;
    else if (tcolor == I_B || tcolor == I_AB) lnode = y;

    if (tcolor == I_B || tcolor == I_AB) rnode = y;
    else if (scolor == I_B || scolor == I_AB) rnode = x;

    bool rfound = false;

    if (rnode != nullptr) rfound = true;

    if (lnode == nullptr || rnode == nullptr) {
        for (std::size_t i = 0; i < sorted_edges.size(); ++i) {
            scolor = sorted_edges[i]->source->color;
            tcolor = sorted_edges[i]->target->color;

            if (lnode == nullptr) {
                if (scolor == I_B || scolor == I_AB) lnode = sorted_edges[i]->source;
                else if (tcolor == I_B || tcolor == I_AB) lnode = sorted_edges[i]->target;
            }

            if (!rfound) {
                if (tcolor == I_B || tcolor == I_AB) rnode = sorted_edges[i]->target;
                else if (scolor == I_B || scolor == I_AB) rnode = sorted_edges[i]->source;
            }
        }
    }

    if (lnode == nullptr || rnode == nullptr || lnode == rnode) {
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
    vector<CEdge *> sorted_edges;
    getSortedEdges(x, y, sorted_edges);

    CNode * lnode = nullptr;
    CNode * rnode = nullptr;

    icolor_t scolor = x->color;
    icolor_t tcolor = y->color;

    if (scolor == I_A || scolor == I_AB) lnode = x;
    else if (tcolor == I_A || tcolor == I_AB) lnode = y;

    if (tcolor == I_A || tcolor == I_AB) rnode = y;
    else if (scolor == I_A || scolor == I_AB) rnode = x;

    bool rfound = false;

    if (rnode != nullptr) rfound = true;

    if (lnode == nullptr || rnode == nullptr) {
        for (std::size_t i = 0; i < sorted_edges.size(); ++i) {
            scolor = sorted_edges[i]->source->color;
            tcolor = sorted_edges[i]->target->color;

            if (lnode == nullptr) {
                if (scolor == I_A || scolor == I_AB) lnode = sorted_edges[i]->source;
                else if (tcolor == I_A || tcolor == I_AB) lnode = sorted_edges[i]->target;
            }

            if (!rfound) {
                if (tcolor == I_A || tcolor == I_AB) rnode = sorted_edges[i]->target;
                else if (scolor == I_A || scolor == I_AB) rnode = sorted_edges[i]->source;
            }
        }
    }

    if (lnode == nullptr || rnode == nullptr || lnode == rnode) {
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
UFInterpolator::J(const path_t & p, vector<path_t> & b_paths) {
    // True on empty path
    if (p.first == p.second) return logic.getTerm_true();

    vec<PTRef> conj;

    for (unsigned i = 0; i < b_paths.size(); i++) {
        conj.push(logic.mkEq(b_paths[i].first->e, b_paths[i].second->e));
        //  conj.push_back( egraph.mkEq( egraph.cons( b_paths[ i ].first->e
        //                       , egraph.cons( b_paths[ i ].second->e ) ) ) );
    }

    PTRef implicant = logic.mkAnd(conj);
    //PTRef implicant = egraph.mkAnd( egraph.cons( conj ) );
    PTRef implicated = logic.mkEq(p.first->e, p.second->e);
    //PTRef implicated = egraph.mkEq( egraph.cons( p.first->e, egraph.cons( p.second->e ) ) );

    // Notice that it works also for A-paths like
    //
    // false --> (<= x0 1) --> (<= 2 1)
    //
    // this path says that (<= 2 1) is false, so the implicated
    // should be (not (<= 2 1))

    PTRef res = logic.mkImpl(implicant, implicated);
    //PTRef res = egraph.mkImplies( egraph.cons( implicant, egraph.cons( implicated ) ) );
    return res;
}

PTRef
UFInterpolator::Iprime(const path_t & pi) {
    vec<PTRef> conj;
    // Compute largest subpath of c1 -- c2
    // with B-colorable endpoints
    path_t pi_1, pi_2, theta;
    bool empty_theta = !getSubpaths(pi, pi_1, theta, pi_2);
    // Compute B( pi_1 ) U B( pi_2 )
    vector<path_t> b_paths;
    B(pi_1, b_paths);
    B(pi_2, b_paths);

    if (!empty_theta) {
        conj.push(I(theta));
    }

    for (unsigned i = 0; i < b_paths.size(); i++)
        conj.push(I(b_paths[i]));

    // Finally compute implication
    vec<PTRef> conj_impl;

    for (unsigned i = 0; i < b_paths.size(); i++) {
        conj_impl.push(logic.mkEq(b_paths[i].first->e, b_paths[i].second->e));
    }

    PTRef implicant = logic.mkAnd(conj_impl);
    PTRef implicated = PTRef_Undef;

    if (empty_theta)
        implicated = logic.getTerm_false();
    else
        implicated = logic.mkNot(logic.mkEq(theta.first->e, theta.second->e));

    conj.push(logic.mkImpl(implicant, implicated));
    return logic.mkAnd(conj);
}

PTRef
UFInterpolator::IprimeSwap(const path_t & pi) {
    vec<PTRef> conj;
    // Compute largest subpath of c1 -- c2
    // with B-colorable endpoints
    path_t pi_1, pi_2, theta;
    bool empty_theta = !getSubpathsSwap(pi, pi_1, theta, pi_2);
    // Compute B( pi_1 ) U B( pi_2 )
    vector<path_t> b_paths;
    BSwap(pi_1, b_paths);
    BSwap(pi_2, b_paths);

    if (!empty_theta) {
        conj.push(ISwap(theta));
    }

    for (unsigned i = 0; i < b_paths.size(); i++)
        conj.push(ISwap(b_paths[i]));

    // Finally compute implication
    vec<PTRef> conj_impl;

    for (unsigned i = 0; i < b_paths.size(); i++) {
        conj_impl.push(logic.mkEq(b_paths[i].first->e, b_paths[i].second->e));
    }

    PTRef implicant = logic.mkAnd(conj_impl);
    PTRef implicated = PTRef_Undef;

    if (empty_theta)
        implicated = logic.getTerm_false();
    else
        implicated = logic.mkNot(logic.mkEq(theta.first->e, theta.second->e));

    conj.push(logic.mkImpl(implicant, implicated));
    return logic.mkAnd(conj);
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
    vector<path_t> factors;
    factors.push_back(p);
    // Will store parents of B-path
    vector<path_t> parents;

    const bool a_factor = getFactorsAndParents(p, factors, parents);

    if (factors.size() == 1) {
        // It's an A-path
        if (a_factor) {
            // Compute J
            vector<path_t> b_premise_set;
            B(p, b_premise_set);
            conj.push(J(p, b_premise_set));

            for (unsigned i = 0; i < b_premise_set.size(); i++) {
                path_t & fac = b_premise_set[i];
                assert (L.find(fac) != L.end());

                if (L[fac] == I_B) {
                    conj.push(Irec(b_premise_set[i], cache));
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
            for (unsigned i = 0; i < parents.size(); i++)
                conj.push(Irec(parents[i], cache));
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

                vector<path_t> infactors;
                infactors.push_back(pf);
                vector<path_t> inparents;
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

                if (l->color == I_A) la = true;
                else if (l->color == I_B) lb = true;
                else lab = true;

                if (r->color == I_A) ra = true;
                else if (r->color == I_B) rb = true;
                else rab = true;

                assert (!((la && rb) || (lb && ra)));
                bool b = true;//rand() % 2;

                if (la || ra) // conflict in A, call I' or not S
                {
                    assert (i == 0 || j == (factors.size() - 1));

                    if (b && config.itp_euf_alg() == 4) {
                        conj.push(Irec(pf, cache));
                    } else {
                        conj.push(logic.mkNot(IprimeSwap(pf)));
                    }
                } else if (lb || rb) // conflict in B, call I or not S'
                {
                    assert (i == 0 || j == (factors.size() - 1));

                    if (b && config.itp_euf_alg() == 4) {
                        conj.push(Irec(pf, cache));
                    } else {
                        conj.push(logic.mkNot(IprimeSwap(pf)));
                    }
                } else // conflict has global endpoints
                {
                    if (b && config.itp_euf_alg() == 4) {
                        conj.push(Irec(pf, cache));
                    } else {
                        conj.push(logic.mkNot(IprimeSwap(pf)));
                    }
                }
            }
        } else {
            for (std::size_t i = 0; i < factors.size(); ++i)
                conj.push(Irec(factors[i], cache));
        }
    }

    PTRef res = logic.mkAnd(conj);
    assert (res != PTRef_Undef);
    return res;
}

PTRef
UFInterpolator::IrecSwap(const path_t & p, map<path_t, PTRef> & cache) {
    // True on empty path
    if (p.first == p.second) return logic.getTerm_true();

    vec<PTRef> conj;
    vec<PTRef> conj_swap;
    // Will store factors
    vector<path_t> factors;
    factors.push_back(p);
    // Will store parents of A-path
    vector<path_t> parents;

    const bool a_factor = getFactorsAndParents(p, factors, parents);

    if (factors.size() == 1) {
        // It's a B-path
        if (!a_factor) {
            // Compute J
            vector<path_t> b_premise_set;
            BSwap(p, b_premise_set);
            conj.push(J(p, b_premise_set));
            for (unsigned i = 0; i < b_premise_set.size(); i++) {
                path_t & fac = b_premise_set[i];
                assert (L.find(fac) != L.end());

                if (L[fac] == I_A) {
                    conj.push(IrecSwap(fac, cache));
                } else {
                    conj_swap.push(logic.mkNot(Iprime(fac)));
                }
            }

            if (conj_swap.size() > 0) {
                conj.push(logic.mkAnd(conj_swap));
            }
        }
            // It's an A-path
        else {
            // Recurse on parents
            for (unsigned i = 0; i < parents.size(); i++) {
                conj.push(IrecSwap(parents[i], cache));
            }
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

                vector<path_t> infactors;
                infactors.push_back(pf);
                vector<path_t> inparents;
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

                if (l->color == I_A) la = true;
                else if (l->color == I_B) lb = true;
                else lab = true;

                if (r->color == I_A) ra = true;
                else if (r->color == I_B) rb = true;
                else rab = true;

                assert (!((la && rb) || (lb && ra)));
                bool b = true;//rand() % 2;

                if (la || ra) {
                    assert (i == 0 || j == (factors.size() - 1));

                    if (b && config.itp_euf_alg() == 4) {
                        conj.push(logic.mkNot(Iprime(pf)));
                    } else {
                        conj.push(IrecSwap(pf, cache));
                    }
                } else if (lb || rb) {
                    assert (i == 0 || j == (factors.size() - 1));

                    if (b && config.itp_euf_alg() == 4) {
                        conj.push(logic.mkNot(Iprime(pf)));
                    } else {
                        conj.push(IrecSwap(pf, cache));
                    }
                } else // conflict has global endpoints
                {
                    if (b && config.itp_euf_alg() == 4) {
                        conj.push(logic.mkNot(Iprime(pf)));
                    } else {
                        conj.push(IrecSwap(pf, cache));
                    }
                }
            }
        } else {

            for (std::size_t i = 0; i < factors.size(); ++i) {
                conj.push(IrecSwap(factors[i], cache));
            }
        }
    }

    PTRef res = logic.mkAnd(conj);
    assert (res != PTRef_Undef);
    return res;
}

void UFInterpolator::B(const path_t & p, vector<path_t> & b_premise_set) {
    set<path_t> cache;
    Brec(p, b_premise_set, cache);
}

void UFInterpolator::BSwap(const path_t & p, vector<path_t> & a_premise_set) {
    set<path_t> cache;
    BrecSwap(p, a_premise_set, cache);
}

void UFInterpolator::Brec(const path_t & p, vector<path_t> & b_premise_set, set<path_t> & cache) {
    // Skip trivial call
    if (p.first == p.second) return;

    // Skip seen calls
    if (!cache.insert(p).second) return;

    // Will store factors
    vector<path_t> factors;
    factors.push_back(p);
    // Will store parents of B-path
    vector<path_t> parents;

    const bool a_factor = getFactorsAndParents(p, factors, parents);

    if (factors.size() == 1) {
        // It's an A-path
        if (a_factor) {
            for (unsigned i = 0; i < parents.size(); i++)
                Brec(parents[i], b_premise_set, cache);
        }
            // It's a B-path
        else
            b_premise_set.push_back(p);
    } else {
        // Recurse on factors
        for (unsigned i = 0; i < factors.size(); i++)
            Brec(factors[i], b_premise_set, cache);
    }
}

void UFInterpolator::BrecSwap(const path_t & p, vector<path_t> & a_premise_set, set<path_t> & cache) {
    // Skip trivial call
    if (p.first == p.second) return;

    // Skip seen calls
    if (!cache.insert(p).second) return;

    // Will store factors
    vector<path_t> factors;
    factors.push_back(p);
    // Will store parents of B-path
    vector<path_t> parents;

    const bool a_factor = getFactorsAndParents(p, factors, parents);

    if (factors.size() == 1) {
        // It's an A-path
        if (!a_factor) {
            for (unsigned i = 0; i < parents.size(); i++)
                BrecSwap(parents[i], a_premise_set, cache);
        }
            // It's a B-path
        else
            a_premise_set.push_back(p);
    } else {
        // Recurse on factors
        for (unsigned i = 0; i < factors.size(); i++)
            BrecSwap(factors[i], a_premise_set, cache);
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

    while (!done) {
        // Advance x by 1
        if (x->next != nullptr) {
            CEdge * candidate = x->next;
            x = x->next->target;

            // Touching an already seen node (by y)
            // x is the nearest common ancestor
            // Clear y vector until x is found
            if (!visited.insert(x).second) {
                while (!tmp.empty() && tmp.back()->target != x) {
                    tmp.pop_back();
                }
                done = true;
            }

            from_x.push_back(candidate);
        }

        if (done) break;

        // Advance y by 1
        if (y->next != nullptr) {
            CEdge * candidate = y->next;
            y = y->next->target;
            // Touching an already seen node (by x)
            // y is the nearest common ancestor
            // Clear x vector until y is found
            if (!visited.insert(y).second) {
                while (!from_x.empty() && from_x.back()->target != y) {
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
    assert (!tmp.empty() || sorted_edges.back()->target == y);
    assert (!sorted_edges.empty() || tmp.back()->target == x);
    assert (sorted_edges.empty()
            || tmp.empty()
            || sorted_edges.back()->target == tmp.back()->target);

    // Now load edges from y in the correct order
    while (!tmp.empty()) {
        sorted_edges.push_back(tmp.back());
        tmp.pop_back();
    }

    return x_path_length;
}

icolor_t UFInterpolator::resolveABColor() const {
    if (usingStrong()) {
        return I_B;
    } else if (usingWeak()) {
        return I_A;
    } else if (usingRandom()) {
        return (rand() % 2) ? I_A : I_B;
    } else {
        assert(false);
        return I_B;
    }
}

//
// Return the set of factors
bool UFInterpolator::getFactorsAndParents(const path_t & p, vector<path_t> & factors, vector<path_t> & parents) {
    assert (factors.size() == 1);
    assert (parents.size() == 0);
    CNode * x = p.first;
    CNode * y = p.second;
    assert (x);
    assert (y);
    vector<CEdge *> sorted_edges;
    const size_t x_path_length = getSortedEdges(x, y, sorted_edges);

    const bool a_factor = sorted_edges[0]->color == I_A;
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
        Pterm & px = logic.getPterm(tx->e);
        Pterm & pn = logic.getPterm(tn->e);

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
            Pterm & px = logic.getPterm(x->e);
            Pterm & pn = logic.getPterm(n->e);

            for (int j = 0; j < px.size(); ++j) {
                PTRef arg_x = px[j];
                PTRef arg_n = pn[j];

                if (arg_n == arg_x) continue;

                // Add parents for further recursion
                parents.push_back(path(cgraph.getNode(arg_x), cgraph.getNode(arg_n)));
            }
        }

        // New factor
        if (i < sorted_edges.size()
            && sorted_edges[i]->color != last_color) {
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
        for (std::size_t i = 0; i < factors.size(); ++i)
            L[factors[i]] = I_B;

        // McMillan'
    else if (usingWeak())
        for (std::size_t i = 0; i < factors.size(); ++i)
            L[factors[i]] = I_A;

        // Random
    else if (usingRandom()) {
        for (std::size_t i = 0; i < factors.size(); ++i) {
            if (rand() % 2) {
                L[factors[i]] = I_B;
            } else {
                L[factors[i]] = I_A;
            }
        }
    }
}

void UFInterpolator::printAsDotty(ostream & os) {
    os << "digraph cgraph {" << endl;

    // Print all nodes
    for (CNode * c : cgraph.getNodes()) {
        string color = "grey";

        if (c->color == I_A) color = "red";

        if (c->color == I_B) color = "blue";

        if (c->color == I_AB) color = "green";

        os << logic.getPterm(c->e).getId().x
           << " [label=\""
           << logic.pp(c->e)
           << "\",color=\"" << color
           << "\",style=filled]"
           << endl;
    }

    // Print all edges
    for (CEdge * c : cgraph.getEdges()) {
        string color = "grey";

        if (c->color == I_A) color = "red";

        if (c->color == I_B) color = "blue";

        if (c->color == I_AB) color = "green";

        os << logic.getPterm(c->source->e).getId().x
           << " -> "
           << logic.getPterm(c->target->e).getId().x
           << " [color=\"" << color
           << "\",style=\"bold"
           << (c->reason == PTRef_Undef ? ",dashed" : "")
           << "\"]"
           << endl;
    }

    // Print conflict
    os << logic.pp(cgraph.getConflictStart()->e)
       << " -> "
       << logic.pp(cgraph.getConflictEnd()->e)
       << " [style=bold]"
       << endl;
    os << "}" << endl;
}

bool UFInterpolator::checkColors() {
    for (CEdge * edge : cgraph.getEdges()) {
        // Edge that is not involved
        if (edge->color == I_UNDEF)
            continue;

        // Check color is A or B
        if (edge->color != I_A && edge->color != I_B)
            return false;

        // Check color is consistent with nodes
        if ((edge->color & edge->source->color) == 0
            || (edge->color & edge->target->color) == 0) {
            // cerr << "edge col " << (*it)->color << endl;
            // cerr << "   s col " << (*it)->source->color << endl;
            // cerr << "   t col " << (*it)->target->color << endl;
            // cerr << "Edge inconsistent colors: " << (*it) << endl;
            return false;
        }
    }
    return true;
}
