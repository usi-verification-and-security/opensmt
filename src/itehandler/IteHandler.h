//
// Created by Martin Blicha on 18.05.21.
//

#ifndef OPENSMT_ITEHANDLER_H
#define OPENSMT_ITEHANDLER_H

#include "PTRef.h"
#include "Logic.h"

#include <unordered_map>

class IteHandler {
private:
    Logic & logic;

    std::string suffix;

    PTRef getAuxVarFor(PTRef ite);

    PTRef replaceItes(PTRef root);

public:

    IteHandler(Logic & logic) : logic(logic) {}

    IteHandler(Logic & logic, unsigned long partitionNumber) : logic(logic), suffix('_' + std::to_string(partitionNumber)) {}

    PTRef rewrite(PTRef root);

    static PTRef getIteTermFor(Logic const & logic, PTRef auxVar); // The inverse of getAuxVarFor

    static std::string_view constexpr itePrefix = ".ite";
};

#endif //OPENSMT_ITEHANDLER_H
