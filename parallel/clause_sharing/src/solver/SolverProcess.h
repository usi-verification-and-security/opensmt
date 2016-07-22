//
// Created by Matteo on 21/07/16.
//

#ifndef CLAUSE_SHARING_PROCESSSOLVER_H
#define CLAUSE_SHARING_PROCESSSOLVER_H

#include "Settings.h"
#include "lib/Process.h"




// devo decidere se passare al costruttore l'header del command solve e l'istanza, ma non so come gestire le variabili
// d'istanza.
class SolverProcess : public Process {
private:
    Settings &settings;
    std::map<std::string, std::string> header;

protected:
    void main();

public:
    SolverProcess(Settings &, std::map<std::string, std::string>);

    std::string toString();

    static constexpr const char *solver = "OpenSMT2";
    const std::string name;
    const std::string hash;
    std::string instance;
    const uint32_t seed;
};

#endif //CLAUSE_SHARING_PROCESSSOLVER_H
