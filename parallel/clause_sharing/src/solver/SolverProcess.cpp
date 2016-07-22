//
// Created by Matteo on 10/12/15.
//

#include <unistd.h>
#include "Interpret.h"
#include "lib/Log.h"
#include "SolverProcess.h"


SolverProcess::SolverProcess(Settings &settings, std::map<std::string, std::string> &header, std::string &instance) :
        Process(),
        settings(settings),
        name(header["name"]),
        hash(header["hash"]),
        instance(instance),
        seed(seed) {
    this->start();
}

std::string SolverProcess::toString() {
    return "SolverProcess<" + std::string(SolverProcess::solver) + ">" + this->name + "(" + this->hash + ")";
}

void SolverProcess::main() {
    std::map<std::string, std::string> header;
    std::string payload = "";

    std::uniform_int_distribution<uint32_t> randuint(0, 0xFFFFFF);
    std::random_device rd;
    SMTConfig config;
    uint32_t seed = randuint(rd);
    config.setRandomSeed(seed);
    Interpret interpret = Interpret(&config);


    this->reader()->read(header, payload);
    header["name"] = this->name;
    header["hash"] = this->hash;
    header["status"] = "sat";

    if (this->settings.get_clause_agent())
        this->settings.get_clause_agent()->write(header, payload);
    sleep(1);
    this->writer()->write(header, payload);

//    std::cerr << "Started job " << this->channel << "\n";
//
//    sstat status = s_Undef;
//    char *msg = NULL;
//
//    std::uniform_int_distribution<uint32_t> randuint(0, 0xFFFFFF);
//    std::random_device rd;
//    SMTConfig config;
//    uint32_t seed = randuint(rd);
//    config.setRandomSeed(seed);
//
//    //Theory *theory = new UFTheory(config);
//    Theory *theory = new LRATheory(config);
//
//    MainSolver *solver = NULL;
//    try {
//        solver = new MainSolver(
//                *theory,
//                config,
//                new _SMTSolver(this->settings, this->channel, config, theory->getTHandler()));
//    }
//    catch (Exception ex) {
//        msg = strdup(ex.what());
//        goto done;
//    }
//
//    solver->initialize();
//    if (solver->readSolverState((int *) this->osmt2.c_str(), (int) this->osmt2.size(), true, &msg)) {
//        status = solver->simplifyFormulas(&msg);
//        if (status != s_True && status != s_False)
//            status = solver->solve();
//    }
//
//    delete solver;
//
//    done:
//
//    Message message;
//    message.header["status"] = std::to_string((int) status.getValue());
//    message.header["msg"] = msg == NULL ? std::string() : std::string(msg);
//    message.header["channel"] = this->channel;
//    message.header["seed"] = std::to_string(seed);
//    std::string s;
//    message.dump(s);
//    this->writer().write(s);
//    free(msg);
//
//    std::cout << "Finished job\n";

}

