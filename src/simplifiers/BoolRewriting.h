//
// Created by Martin Blicha on 20.10.18.
//

#ifndef OPENSMT_BOOLREWRITING_H
#define OPENSMT_BOOLREWRITING_H

#include <PTRef.h>

class Logic;

void computeIncomingEdges(const Logic& logic, PTRef tr, Map<PTRef,int,PTRefHash>& PTRefToIncoming);

PTRef rewriteMaxArity(Logic & logic, PTRef root, const Map<PTRef,int,PTRefHash>& PTRefToIncoming);

PTRef mergePTRefArgs(Logic & logic, PTRef tr, Map<PTRef,PTRef,PTRefHash>& cache, const Map<PTRef,int,PTRefHash>& PTRefToIncoming);

#endif //OPENSMT_BOOLREWRITING_H
