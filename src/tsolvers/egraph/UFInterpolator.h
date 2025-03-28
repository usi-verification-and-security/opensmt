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
/* Based on the paper
 * @article{DBLP:journals/corr/abs-1111-5652,
 *    author    = {Alexander Fuchs and Amit Goel and Jim Grundy and Sava Krstic and
 *                 Cesare Tinelli},
 *    title     = {Ground interpolation for the theory of equality},
 *    journal   = {Logical Methods in Computer Science},
 *    volume    = {8},
 *    number    = {1},
 *    year      = {2012},
 *    ee        = {http://dx.doi.org/10.2168/LMCS-8(1:6)2012},
 *    bibsource = {DBLP, http://dblp.uni-trier.de}
 *  }
 */

#ifndef UF_INTERPOLATOR_H
#define UF_INTERPOLATOR_H

#include <options/SMTConfig.h>
#include <pterms/PTRef.h>
#include <smtsolvers/TheoryInterpolator.h>
#include <api/PartitionManager.h>

#include <set>

namespace opensmt {

struct CEdge;
class Logic;

struct CNode {
    CNode(PTRef e_)
        :
        e(e_), color(icolor_t::I_UNDEF), edge(nullptr)
        { }

    PTRef e;
    icolor_t color;
    CEdge * edge;
};

typedef std::pair<CNode *, CNode *> path_t;

struct CEdge {
    CEdge(CNode * s, CNode * t, PTRef r)
        : source(s), target(t), reason(r), color(icolor_t::I_UNDEF) {
        assert(source);
        assert(target);
    }

    CNode * source;
    CNode * target;
    PTRef reason;
    icolor_t color;
};

class CGraph {
    std::vector<CNode *>          cnodes;
    std::vector<CEdge *>          cedges;
    std::map<PTRef, CNode *> cnodes_store;

    PTRef conf1 = PTRef_Undef;
    PTRef conf2 = PTRef_Undef;

    void clear();

public:
    std::vector<CNode *> const & getNodes() const { return cnodes; }
    std::vector<CEdge *> const & getEdges() const { return cedges; }
    bool hasNode(PTRef term) const { return cnodes_store.find(term) != cnodes_store.end(); }
    CNode * getNode(PTRef term) const { return cnodes_store.at(term); }

    CNode * addCNode (PTRef e);
    void  addCEdge (PTRef, PTRef, PTRef);
    void  addCEdge (CNode *, CNode *, PTRef);

    void removeCEdge(CEdge *);

    CNode* getConflictStart() const { assert(conf1 != PTRef_Undef); return cnodes_store.at(conf1); }
    CNode* getConflictEnd()   const { assert(conf2 != PTRef_Undef); return cnodes_store.at(conf2); }

    inline void setConf(PTRef c1, PTRef c2) {
//      cout << "SetConf: " << logic.printTerm(c1) << " = " << logic.printTerm(c2) << endl;
        assert(conf1 == PTRef_Undef);
        assert(conf2 == PTRef_Undef);
        assert(c1 != PTRef_Undef);
        assert(c2 != PTRef_Undef);
        conf1 = c1;
        conf2 = c2;
    }

    ~CGraph( ) { clear( ); }
};

class UFInterpolator : public TheoryInterpolator {
public:

    UFInterpolator(SMTConfig & config_, Logic & logic_, CGraph & cgraph)
        : config(config_), logic(logic_), cgraph(cgraph) {}

    inline int verbose() const { return config.verbosity(); }

    PTRef getInterpolant(const ipartitions_t &, ItpColorMap *, PartitionManager &) override;

    void printAsDotty(std::ostream &);

private:
    icolor_t getLitColor(PTRef term) const {
        assert(litColors.find(term) != litColors.end());
        return litColors.at(term);
    }

    icolor_t getTermColor(PTRef term) const {
        assert(colorInfo);
        return colorInfo->getColorFor(term);
    }

    icolor_t determineDisequalityColor(PTRef t1, PTRef t2, ItpColorMap const & conflictColors) const;

    void colorCGraph();
    void colorNodes();
    icolor_t colorNode(CNode * c);
    bool colorEdges(CNode * c1, CNode * c2);
    bool colorEdgesFrom(CNode * x);
    void colorCongruenceEdge(CEdge * edge);

    void splitEdge(CEdge * edge, PTRef intermediateTerm);

    size_t getSortedEdges(CNode *, CNode *, std::vector<CEdge *> &);

    icolor_t resolveABColor() const;

    bool usingStrong()  const { return config.getEUFInterpolationAlgorithm() == itp_euf_alg_strong; }
    bool usingWeak()    const { return config.getEUFInterpolationAlgorithm() == itp_euf_alg_weak; }
    bool usingRandom()  const { return config.getEUFInterpolationAlgorithm() == itp_euf_alg_random; }

    bool getSubpaths(const path_t &, path_t &, path_t &, path_t &);

    bool getSubpathsSwap(const path_t &, path_t &, path_t &, path_t &);

    PTRef I(const path_t &);
    PTRef Iprime(const path_t &);
    PTRef ISwap(const path_t &);
    PTRef IprimeSwap(const path_t &);
    PTRef Irec(const path_t & p, std::map<path_t, PTRef> & cache);
    PTRef IrecSwap(const path_t & p, std::map<path_t, PTRef> & cache);
    PTRef J(const path_t &, std::vector<path_t> &);
    PTRef JSwap(const path_t &, std::vector<path_t> &);

    void B(const path_t &, std::vector<path_t> &);
    void BSwap(const path_t &, std::vector<path_t> &);
    void Brec(const path_t &, std::vector<path_t> &, std::set<path_t> &);
    void BrecSwap(const path_t &, std::vector<path_t> &, std::set<path_t> &);

    bool getFactorsAndParents(const path_t &, std::vector<path_t> &, std::vector<path_t> &);

    void labelFactors(std::vector<path_t> &);

    inline path_t path(CNode * c1, CNode * c2) { return {c1, c2}; }

    bool checkColors() const;

    SMTConfig & config;
    Logic & logic;
    CGraph & cgraph;
    ItpColorMap litColors; // MB: this is needed because edges need to be colored exactly as the literals in the conflict
    std::set<CNode *> colored_nodes;
    std::set<CEdge *> colored_edges;
    std::unique_ptr<TermColorInfo> colorInfo;
    std::map<path_t, icolor_t> L;

};

}

#endif
