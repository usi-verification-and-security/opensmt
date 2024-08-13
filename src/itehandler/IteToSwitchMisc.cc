//
// Created by prova on 02.09.20.
//

#include "IteToSwitch.h"

#include <fstream>

namespace opensmt::ite {
void Dag::writeDagToStream(std::ostream & out) const {
    std::string annotations_str;
    std::string edges_str;
    auto & nodes = getNodes();
    std::cout << "Starting production of a graph" << std::endl;
    for (NodeRef const node : nodes) {
        if (isTopLevelIte(na[node].getTerm())) {
            annotations_str += " " + std::to_string(na[node].getId()) + " [shape=box];\n";
        }
        if (na[node].getTrueChild() != NodeRef_Undef) {
            edges_str += " " + std::to_string(na[node].getId()) + " -> " +
                         std::to_string(na[na[node].getTrueChild()].getId()) + ";\n";
        }
        if (na[node].getFalseChild() != NodeRef_Undef) {
            edges_str += " " + std::to_string(na[node].getId()) + " -> " +
                         std::to_string(na[na[node].getFalseChild()].getId()) + ";\n";
        }
    }
    out << "digraph G {" << annotations_str << "\n" << edges_str << "}" << std::endl;
}
} // namespace opensmt::ite

namespace opensmt {
void IteToSwitch::printDagToFile(std::string const & fname, ite::Dag const & dag) {
    std::fstream fs;
    fs.open(fname, std::fstream::out);
    dag.writeDagToStream(fs);
    fs.close();
}
} // namespace opensmt
