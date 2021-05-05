//
// Created by prova on 01.04.21.
//

#include <LookaheadSplitter.h>
#include "MainSplitter.h"
#include "SplitData.h"
#include "ScatterSplitter.h"

bool MainSplitter::writeSolverSplits_smtlib2(const char* file, char** msg) const
{
    //std::vector<SplitData>& scattersplits= scatter_Splitter->splits;
    std::vector<SplitData>& splits =(config.sat_split_type()==spt_scatter) ? static_cast<ScatterSplitter&>(ts.solver).splits
            : static_cast<LookaheadSplitter&>(ts.solver).splits;
    if(config.sat_split_type() == spt_scatter)
        std::cout <<"Number of splits created by scatter splitter: "<< splits.size() << "\n";
    int i = 0;
    for (const auto & split : splits) {
        vec<PTRef> conj_vec;
        std::vector<vec<PtAsgn> > constraints;
        split.constraintsToPTRefs(constraints, thandler);
        addToConj(constraints, conj_vec);

        std::vector<vec<PtAsgn> > learnts;
        split.learntsToPTRefs(learnts, thandler);
        addToConj(learnts, conj_vec);

        if (config.smt_split_format_length() == spformat_full)
            conj_vec.push(root_instance.getRoot());

        PTRef problem = logic.mkAnd(conj_vec);

        char* name;
        int written = asprintf(&name, "%s-%02d.smt2", file, i ++);
        assert(written >= 0);
        (void)written;
        std::ofstream file;
        file.open(name);
        if (file.is_open()) {
            logic.dumpHeaderToFile(file);
            logic.dumpFormulaToFile(file, problem);

            if (config.smt_split_format_length() == spformat_full)
                logic.dumpChecksatToFile(file);

            file.close();
        }
        else {
            written = asprintf(msg, "Failed to open file %s\n", name);
            assert(written >= 0);
            free(name);
            return false;
        }
        free(name);
    }
    return true;
}
