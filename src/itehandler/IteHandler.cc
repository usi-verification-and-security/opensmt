//
// Created by Martin Blicha on 18.05.21.
//

#include "IteHandler.h"
#include "IteToSwitch.h"

#include <common/InternalException.h>

namespace opensmt {
PTRef IteHandler::rewrite(PTRef root) {
    IteToSwitch switches(logic, root);
    PTRef new_root = switches.conjoin(root);
    return new_root == root ? root : replaceItes(new_root);
}

PTRef IteHandler::getAuxVarFor(PTRef ite) {
    assert(logic.isIte(ite));
    std::string name(itePrefix);
    name += std::to_string(ite.x);
    name += suffix;
    return logic.mkVar(logic.getSortRef(ite), name.c_str());
}

PTRef IteHandler::getIteTermFor(Logic const & logic, PTRef auxVar) {
    std::string const & name = logic.getSymName(auxVar);
    assert(name.compare(0, itePrefix.size(), itePrefix) == 0);
    std::string numberStr;
    for (auto it = name.begin() + itePrefix.size(); it != name.end(); ++it) {
        if ('0' <= *it and *it <= '9') {
            numberStr += *it;
        } else {
            break;
        }
    }
    auto number = static_cast<uint32_t>(std::stoul(numberStr));
    PTRef ite = {number};
    assert(logic.isIte(ite));
    return ite;
}

PTRef IteHandler::replaceItes(PTRef root) {
    // Note: We cannot use the current rewriting infrastructure because here we want to rewrite ITE without
    // analyzing first its children.
    // TODO: adjust rewriting infrastructure to fit this case as well.
    struct DFSEntry {
        DFSEntry(PTRef term) : term(term) {}
        PTRef term;
        unsigned int nextChild = 0;
    };

    // MB: Relies on an invariant that id of a child is lower than id of a parent.
    auto size = Idx(logic.getPterm(root).getId()) + 1;
    std::vector<char> done;
    done.resize(size, 0);
    std::unordered_map<PTRef, PTRef, PTRefHash> substitutions;
    std::vector<DFSEntry> toProcess;
    toProcess.emplace_back(root);
    while (not toProcess.empty()) {
        auto & currentEntry = toProcess.back();
        PTRef currentRef = currentEntry.term;
        auto currentId = Idx(logic.getPterm(currentRef).getId());
        if (logic.isIte(currentRef)) {
            substitutions.insert({currentRef, getAuxVarFor(currentRef)});
            done[currentId] = 1;
            toProcess.pop_back();
            continue;
        }
        assert(not done[currentId]);
        Pterm const & term = logic.getPterm(currentRef);
        unsigned childrenCount = term.size();
        if (currentEntry.nextChild < childrenCount) {
            PTRef nextChild = term[currentEntry.nextChild];
            ++currentEntry.nextChild;
            if (not done[Idx(logic.getPterm(nextChild).getId())]) { toProcess.push_back(DFSEntry(nextChild)); }
            continue;
        }
        // If we are here, we have already processed all children
        assert(done[currentId] == 0);
        vec<PTRef> newArgs(childrenCount);
        bool needsChange = false;
        for (unsigned i = 0; i < childrenCount; ++i) {
            auto it = substitutions.find(term[i]);
            bool childChanged = it != substitutions.end();
            needsChange |= childChanged;
            newArgs[i] = childChanged ? it->second : term[i];
        }
        PTRef newTerm = needsChange ? logic.insertTerm(term.symb(), std::move(newArgs)) : currentRef;
        if (needsChange) { substitutions.insert({currentRef, newTerm}); }
        done[currentId] = 1;
        toProcess.pop_back();
    }

    auto it = substitutions.find(root);
    PTRef res = it == substitutions.end() ? root : it->second;
    return res;
}
} // namespace opensmt
