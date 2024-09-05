#ifndef OPENSMT_H
#define OPENSMT_H

#include "MainSolver.h"

#include <logics/Logic.h>
#include <logics/ArithLogic.h>
#include <options/SMTConfig.h>

#include <memory>

namespace opensmt {

typedef enum
{
    qf_uf         // Uninterpreted Functions
  , qf_bv         // BitVectors
  , qf_rdl        // Real difference logics
  , qf_idl        // Integer difference logics
  , qf_lra        // Real linear arithmetic
  , qf_lia        // Integer linear arithmetic
  , qf_ufrdl      // UF + RDL
  , qf_ufidl      // UF + IDL
  , qf_uflra      // UF + LRA
  , qf_uflia      // UF + LIA
  , qf_ax         // Arrays with extensionality
  , qf_alra       // Arrays + LRA
  , qf_alia       // Arrays + LIA
  , qf_auflra     // Arrays + UF + LRA
  , qf_auflia     // Arrays + UF + LIA
  , qf_bool       // Only booleans
  , qf_auflira    // Arrays + UF + (LIA or LRA)
} opensmt_logic;

class Opensmt {
public:
    Opensmt             (const Opensmt&) = delete;
    Opensmt& operator = (const Opensmt&) = delete;
    Opensmt             (Opensmt&&) = default;
    Opensmt& operator = (Opensmt&&) = default;

    ~Opensmt() = default;

    Opensmt(opensmt_logic _logic, const char* name);

    /**
     * Constructor for OpenSMT instance where user user can passed its open configuration.
     * Useful for example when interpolation needs to be enabled
     * Note that this object takes ownership of the passed pointer
     *
     * @param _logic SMT-LIB logic that OpenSMT instance will operate in
     * @param name Name for the solver instance
     * @param config Configuration for the OpenSMT instance
     */
    Opensmt(opensmt_logic _logic, const char* name, std::unique_ptr<SMTConfig> config);

    SMTConfig& getConfig() { return *config; }
    Logic& getLogic() { return *logic; }
    ArithLogic& getLRALogic() { return dynamic_cast<ArithLogic&>(*logic); }
    ArithLogic& getLIALogic() { return dynamic_cast<ArithLogic&>(*logic); }
    MainSolver& getMainSolver() { return *mainSolver; }
    SimpSMTSolver& getSolver() { return getMainSolver().getSMTSolver(); }
private:
    std::unique_ptr<SMTConfig> config;
    std::unique_ptr<Logic> logic;
    std::unique_ptr<MainSolver> mainSolver;
};

}

#endif //OPENSMT_H
