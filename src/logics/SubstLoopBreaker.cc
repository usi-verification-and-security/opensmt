//
// Created by prova on 21.11.19.
//

#include "SubstLoopBreaker.h"

SNRef SubstNode::getNextChild() {
    if (procChild < nChildren()) return operator[](procChild++);
    return SNRef_Undef;
}

//
// Get all vars from a term.  Guarantees that no variable repeats in the list.
//
vec<PTRef> SubstNodeAllocator::getVars(PTRef term) const
{
    vec<PTRef> vars;
    Map<PTRef, bool, PTRefHash> proc;
    vec<PTRef> queue;
    queue.push(term);

    while (queue.size() != 0) {
        PTRef tr = queue.last();
        if (proc.has(tr)) {
            queue.pop();
            continue;
        }
        bool unprocessed_children = false;
        const Pterm& t = logic.getPterm(tr);
        for (int i = 0; i < t.size(); i++)
            if (!proc.has(t[i])) {
                queue.push(t[i]);
                unprocessed_children = true; }
        if (unprocessed_children) continue;
        queue.pop();
        proc.insert(tr, true);
        if (logic.isVar(tr)) vars.push(tr);
    }
    return vars;
}

SNRef SubstNodeAllocator::alloc(PTRef tr, PTRef target)
{
    SNRef tmp;
    if (SourceToSNRef.peek(tr, tmp))
        return tmp;

    uint32_t v = RegionAllocator<uint32_t>::alloc(substNode32Size());
    SNRef sid = {v};
    TVLRef tvr;
    if (target == PTRef_Undef) {
        new (lea(sid)) SubstNode(tr, PTRef_Undef, vec<PTRef>(), tla);
    }
    else if (TargetToTargetVarListRef.peek(target, tvr)) {
        new (lea(sid)) SubstNode(tr, target, tvr, tla);
    }
    else {
        new (lea(sid)) SubstNode(tr, target, getVars(target), tla);
    }
    SourceToSNRef.insert(tr, sid);
    SNRefs.push(sid);
    return sid;
}

void
SubstNodeAllocator::clearTarjan()
{
    for (int i = 0; i < SNRefs.size(); i++)
        operator[](SNRefs[i]).clearTarjan();
}

TargetVarList::TargetVarList(vec<PTRef>&& _children)
{
    header.sz = (unsigned)_children.size();
    for (int i = 0; i < size(); i++)
        vars[i].t = _children[i];
}

TVLRef TargetVarListAllocator::alloc(vec<PTRef>&& _children)
{
    sort(_children);
    uint32_t v = RegionAllocator<uint32_t>::alloc(targetVarList32Size(_children.size()));
    TVLRef sid = {v};
    auto size = (unsigned)_children.size();
    new (lea(sid)) TargetVarList(std::move(_children));
    operator[](sid).header.proc = 0;
    operator[](sid).header.sz = size;
    return sid;
}

void TarjanAlgorithm::addNode(SNRef n) {
    sna[n].setIndex(index);
    sna[n].setLowLink(index);
    index++;
    controlStack.push(n);
    tarjanStack.push(n);
    sna[n].setStatus(NStatus::inStack);
}

std::vector<vec<SNRef>> TarjanAlgorithm::getLoops(SNRef startNode) {
    std::vector<vec<SNRef>> loops;
    addNode(startNode);
    while (controlStack.size() > 0) {
        SNRef n = controlStack.last();
        SNRef c = sna[n].getNextChild();
        if (c != SNRef_Undef) {
            if (sna[c].getStatus() == NStatus::unseen)
                addNode(c);
            else if (sna[c].getStatus() == NStatus::inStack)
                sna[n].updateLowLink(sna[c].getIndex());
        } else {
            controlStack.pop();
            if (controlStack.size() > 0)
                sna[controlStack.last()].updateLowLink(sna[n].getLowLink());
            if (sna[n].getLowLink() == sna[n].getIndex()) {
                // Start a new SCC
                vec<SNRef> scc;
                SNRef w = SNRef_Undef;
                do {
                    w = tarjanStack.last(); tarjanStack.pop();
                    sna[w].setStatus(NStatus::complete);
                    scc.push(w);
                } while (w != n);
                if (scc.size() > 1) {
                    loops.emplace_back();
                    for (int i = scc.size()-1; i >= 0; i--)
                        loops.back().push(scc[i]);
                }
            }
        }
    }
    return loops;
}


vec<SNRef> SubstLoopBreaker::constructSubstitutionGraph(const MapWithKeys<PTRef,PtAsgn,PTRefHash>& substs)
{
    Map<PTRef, SNRef, PTRefHash> PTRefToSNRef;
    vec<PTRef> PTRefs;

    for (PTRef name : substs.getKeys()) {
        PtAsgn subst = substs[name];

        // Allocate the nodes and create the mapping for each enabled substitution
        if (subst.sgn == l_True) {
            PTRefToSNRef.insert(name, sna.alloc(name, subst.tr));
            PTRefs.push(name);
        }
    }

    vec<SNRef> roots;
    for (int i = 0; i < PTRefs.size(); i++) {
        PTRef var = PTRefs[i];
        SNRef var_node = PTRefToSNRef[var];

        vec<SNRef> queue;
        // The node has already been processed or the substitution is disabled
        if (seen.has(var))
            continue;

        queue.push(var_node);
        roots.push(var_node);

        while (queue.size() > 0) {
            SNRef var_sr = queue.last();
            queue.pop();
            PTRef var_tr = sna[var_sr].getTr();
            if (!seen.has(var_tr)) {
                seen.insert(var_tr, true);
                sna[var_sr].setProcessing();
                for (int j = 0; j < sna[var_sr].nChildren(); j++) {
                    PTRef child_tr = sna[var_sr].getChildTerm(j);
                    SNRef cn = SNRef_Undef;
                    if (PTRefToSNRef.peek(child_tr, cn)) {
                        // The child is already created
                        if (sna[cn].getParent() == SNRef_Undef && cn != var_sr)
                            sna[cn].setParent(var_sr);
                    }
                    else {
                        // The child is not yet created, so create it.
                        // The child cannot have a substitution target since in that case it would have been created.
                        // No need to push it to the queue therefore.
                        cn = sna.alloc(child_tr, PTRef_Undef);
                    }
                    // Update the child to var
                    sna[var_sr][j] = cn;
                    queue.push(cn);
                }
                sna[var_sr].setProcessed();
            }
        }
    }
    return minimizeRoots(std::move(roots));
}

std::vector<vec<SNRef>> SubstLoopBreaker::findLoops(vec<SNRef>& startNodes) {
    std::vector<vec<SNRef>> loops;
    TarjanAlgorithm tarjan(sna);
    for (int i = 0; i < startNodes.size(); i++) {
        std::vector<vec<SNRef>> loops_tmp = tarjan.getLoops(startNodes[i]);
        for (auto & loop : loops_tmp) {
            loops.emplace_back(std::move(loop));
        }
    }
    return loops;
}

MapWithKeys<PTRef,PtAsgn,PTRefHash> SubstLoopBreaker::constructLooplessSubstitution(MapWithKeys<PTRef,PtAsgn,PTRefHash>&& substs)
{
    for (PTRef key : substs.getKeys()) {
        PtAsgn & data = substs[key];
        if (data.sgn != l_True) {
            continue;
        }

        SNRef subst_node = sna.getSNRefBySource(key);
        if (!sna[subst_node].hasChildren())
            data.sgn = l_False;
    }
    return std::move(substs); // Since susbsts is a template, we need the move constructor here
}

//
// Identify and break any substitution loops
//
MapWithKeys<PTRef,PtAsgn,PTRefHash> SubstLoopBreaker::operator() (MapWithKeys<PTRef,PtAsgn,PTRefHash>&& substs)
{
    assert(seen.elems() == 0);

    if (substs.getSize() == 0) return MapWithKeys<PTRef,PtAsgn,PTRefHash>();

    vec<SNRef> startNodes = constructSubstitutionGraph(substs);

    while (true) {
        std::vector<vec<SNRef>> loops = findLoops(startNodes);

        // Terminate if no loops found
        if (loops.size() == 0)
            break;

//        printGraphAndLoops(startNodes, loops);
        vec<SNRef> orphans = breakLoops(loops);
        for (SNRef orphan : orphans)
            startNodes.push(orphan);
        sort(startNodes);
        uniq(startNodes);
//        printGraphAndLoops(startNodes, loops);
    }
    return constructLooplessSubstitution(std::move(substs));
}

vec<SNRef> SubstLoopBreaker::breakLoops(const std::vector<vec<SNRef>>& loops) {
    // Break the found loops.  Return the orphaned children as new start nodes
    vec<SNRef> orphans;
    for (const auto & loop : loops) {
        int last_idx = loop.size()-1;
        assert(last_idx >= 0);
        for (int j = 0; j < sna[loop[last_idx]].nChildren(); j++) {
            orphans.push(sna[loop[last_idx]][j]);
        }
        sna[loop[last_idx]].swipeChildren();
    }
    return orphans;
}

std::string SubstLoopBreaker::printGraphAndLoops(const vec<SNRef> &startNodes, const std::vector<vec<SNRef>>& loops) {
    if (loops.size() == 0)
        cerr << "No loops\n";
    int count = 0;
    for (const vec<SNRef> & loop : loops) {
        cerr << "Loop " << count++ << endl;
        for (SNRef snr: loop)
            cerr << "  " << logic.pp(sna[snr].getTr()) << endl;
    }
    stringstream ss;

    // Debug: visualize a bit.

    ss << "digraph foo {\n";
    for (int i = 0; i < startNodes.size(); i++) {
        char *n = logic.pp(sna[startNodes[i]].getTr());
        ss << "  " << n << " [shape=box]\n";
        free(n);
    }

    Map<PTRef,bool,PTRefHash> seen;

    for (int i = 0; i < startNodes.size(); i++) {

        vec<SNRef> queue;
        queue.push(startNodes[i]);
        while (queue.size() > 0) {
            SNRef n = queue.last();
            queue.pop();
            PTRef n_tr = sna[n].getTr();
            if (seen.has(n_tr))
                continue;
            seen.insert(n_tr, true);
            for (int j = 0; j < sna[n].nChildren(); j++) {
                SNRef sn = sna[n][j];
                if (sn != SNRef_Undef) {
                    char *in = logic.pp(sna[n].getTr());
                    char *out = logic.pp(sna[sn].getTr());
                    ss << "  " << in << " -> " << out << ";\n";
                    free(in);
                    free(out);
                    queue.push(sn);
                }
            }
        }
    }
    for (const auto & loop : loops) {
        for (int j = 0; j < loop.size()-1; j++) {
            char *in = logic.pp(sna[loop[j]].getTr());
            char *out = logic.pp(sna[loop[(j + 1)]].getTr());
            ss << "  " << in << " -> " << out << " [style=dotted];\n";
            free(in);
            free(out);
        }
        SNRef last = loop[loop.size()-1];
        char* in = logic.pp(sna[last].getTr());
        for (int j = 0; j < sna[last].nChildren(); j++) {
            char* out = logic.pp(sna[sna[last][j]].getTr());
            ss << "  " << in << " -> " << out << " [style=dashed];\n";
            free(out);
        }
        free(in);
    }
    ss << "}";
    return ss.str();
}
