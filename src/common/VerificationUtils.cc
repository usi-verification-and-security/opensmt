//
// Created by Martin Blicha on 29.07.20.
//

#include "VerificationUtils.h"

#include "MainSolver.h"
#include "TreeOps.h"

#include <sys/wait.h>
#include <unistd.h>

bool VerificationUtils::impliesExternal(PTRef implicant, PTRef implicated) const {
    const char * implies = "implies.smt2";
    std::ofstream dump_out( implies );
    logic.dumpHeaderToFile(dump_out);

    logic.dumpFormulaToFile(dump_out, implicant);
    logic.dumpFormulaToFile(dump_out, implicated, true);
    dump_out << "(check-sat)" << '\n';
    dump_out << "(exit)" << '\n';
    dump_out.close( );
    // Check !
    bool tool_res;
    int pid = fork();
    if(pid == -1){
        std::cerr << "Failed to fork\n";
        // consider throwing and exception
        return false;
    }
    else if( pid == 0){
        // child process
        execlp( config.certifying_solver, config.certifying_solver, implies, NULL );
        perror( "Child process error: " );
        exit( 1 );
    }
    else{
        // parent
        int status;
        waitpid(pid, &status, 0);
        switch ( WEXITSTATUS( status ) )
        {
            case 0:
//                std::cerr << "Implication holds!\n";
                tool_res = false;
                break;
            case 1:
//                std::cerr << "Implication does not hold!\n";
//                std::cerr << "Antecedent: " << logic.printTerm(implicant) << '\n';
//                std::cerr << "Consequent: " << logic.printTerm(implicated) << '\n';
                tool_res = true;
                break;
            default:
                perror( "Parent process error" );
                exit( EXIT_FAILURE );
        }
    }

    return !tool_res;
}

bool VerificationUtils::verifyInterpolantExternal(PTRef partA, PTRef partB, PTRef itp) const {
    bool verbose = config.verbosity() > 0;
    if(verbose) {
        std::cout << "; Verifying final interpolant" << std::endl;
    }
    bool res = impliesExternal(partA, itp);
    if(!res) { return false; }
    if(verbose) {
        std::cout << "; A -> I holds" << std::endl;
    }
    res = impliesExternal(itp, logic.mkNot(partB));
    if(!res) { return false; }
    if(verbose) {
        std::cout << "; B -> !I holds" << std::endl;
    }
    return res;
}

bool VerificationUtils::verifyInterpolantInternal(PTRef Apartition, PTRef Bpartition, PTRef itp) {
    SMTConfig validationConfig;
    MainSolver validationSolver(logic, validationConfig, "validator");
//    std::cout << "A part:   " << logic.printTerm(Apartition) << '\n';
//    std::cout << "B part:   " << logic.printTerm(Bpartition) << '\n';
//    std::cout << "Interpol: " << logic.printTerm(itp) << std::endl;
    validationSolver.push();
    validationSolver.insertFormula(logic.mkNot(logic.mkImpl(Apartition, itp)));
    auto res = validationSolver.check();
    bool ok = res == s_False;
    if (not ok) { return false; }
    validationSolver.pop();
    validationSolver.insertFormula(logic.mkNot(logic.mkImpl(itp, logic.mkNot(Bpartition))));
    res = validationSolver.check();
    ok = res == s_False;
    if (not ok) { return false; }
    return checkSubsetCondition(itp, Apartition) and checkSubsetCondition(itp, Bpartition);
}

bool VerificationUtils::checkSubsetCondition(PTRef p1, PTRef p2) const {
    auto vars_p1 = variables(logic, p1);
    auto vars_p2 = variables(logic, p2);
    for (PTRef key : vars_p1) {
        if (std::find(vars_p2.begin(), vars_p2.end(), key) == vars_p2.end()) {
            return false;
        }
    }
    return true;
}

bool VerificationUtils::impliesInternal(PTRef antecedent, PTRef consequent) {
    SMTConfig validationConfig;
    MainSolver validationSolver(logic, validationConfig, "validator");
    validationSolver.insertFormula(logic.mkNot(logic.mkImpl(antecedent, consequent)));
    auto res = validationSolver.check();
    bool valid = res == s_False;
    return valid;
}


