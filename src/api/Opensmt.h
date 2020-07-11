#ifndef OPENSMT_H
#define OPENSMT_H

#include "SMTConfig.h"
#include "Theory.h"
#include "THandler.h"
#include "SimpSMTSolver.h"
#include "MainSolver.h"
#include "Logic.h"

#include <memory>

typedef enum
{
    qf_uf         // Uninterpreted Functions
  , qf_cuf        // Uninterpreted Functions for C
  , qf_bv         // BitVectors
  , qf_rdl        // Real difference logics
  , qf_idl        // Integer difference logics
  , qf_lra        // Real linear arithmetic
  , qf_lia        // Integer linear arithmetic
  , qf_ufidl      // UF + IDL
  , qf_uflra      // UF + LRA
  , qf_bool       // Only booleans
  , qf_ct         // Cost 
} opensmt_logic;

class Opensmt
{
public:
    Opensmt(opensmt_logic _logic, const char* name, int bw = 32);

    /**
     * Constructor for OpenSMT instance where user user can passed its open configuration.
     * Useful for example when interpolation needs to be enabled
     * Note that this object takes ownership of the passed pointer
     *
     * @param _logic SMT-LIB logic that OpenSMT instance will operate in
     * @param name Name fot the solver instance
     * @param config Configuration for the OpenSMT instance
     */
    Opensmt(opensmt_logic _logic, const char* name, std::unique_ptr<SMTConfig> config);
    ~Opensmt();

    SMTConfig& getConfig() { return *config; }
    Logic& getLogic() { return mainSolver->getLogic(); }
    LRALogic& getLRALogic()
    {
        LRATheory& t = (LRATheory&)mainSolver->getTheory();
        return t.getLogic();
    }
    LIALogic& getLIALogic()
    {
        LIATheory& t = (LIATheory&)mainSolver->getTheory();
        return t.getLogic();
    }
    CUFLogic& getCUFLogic() {
        CUFTheory& t = (CUFTheory&)mainSolver->getTheory();
        return t.getLogic();
    }
    MainSolver& getMainSolver() { return *mainSolver; }
    SimpSMTSolver& getSolver() { return getMainSolver().getSMTSolver(); }
private:
    std::unique_ptr<SMTConfig> config;
    std::unique_ptr<MainSolver> mainSolver;
};

#endif //OPENSMT_H
