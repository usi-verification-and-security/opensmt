//
// Created by Martin Blicha on 20.10.18.
//

#ifndef OPENSMT_BOOLREWRITING_H
#define OPENSMT_BOOLREWRITING_H

#include <PTRef.h>
#include <vector>
#include <unordered_map>

class Logic;

void computeIncomingEdges(const Logic& logic, PTRef tr, Map<PTRef,int,PTRefHash>& PTRefToIncoming);

PTRef rewriteMaxArity(Logic & logic, PTRef root, const Map<PTRef,int,PTRefHash>& PTRefToIncoming);

PTRef mergePTRefArgs(Logic & logic, PTRef tr, Map<PTRef,PTRef,PTRefHash>& cache, const Map<PTRef,int,PTRefHash>& PTRefToIncoming);

PTRef simplifyUnderAssignment(Logic & logic, PTRef root, const Map<PTRef,int,PTRefHash>& PTRefToIncoming);

PTRef simplifyUnderAssignment_Aggressive(PTRef root, Logic & logic);

std::vector<PTRef> getPostOrder(PTRef root, Logic& logic);

std::unordered_map<PTRef, PTRef, PTRefHash> getImmediateDominators(PTRef root, Logic & logic);

#endif //OPENSMT_BOOLREWRITING_H
