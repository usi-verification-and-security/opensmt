//
// Created by Martin Blicha on 29.07.20.
//

#include "VerificationUtils.h"

#include <sys/wait.h>

bool VerificationUtils::implies(PTRef implicant, PTRef implicated) {
    const char * implies = "implies.smt2";
    std::ofstream dump_out( implies );
    logic.dumpHeaderToFile(dump_out);

    logic.dumpFormulaToFile(dump_out, implicant);
    logic.dumpFormulaToFile(dump_out, implicated, true);
    dump_out << "(check-sat)" << endl;
    dump_out << "(exit)" << endl;
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

bool VerificationUtils::verifyInterpolant(PTRef partA, PTRef partB, PTRef itp) {
    bool verbose = config.verbosity() > 0;
    if(verbose) {
        std::cout << "; Verifying final interpolant" << std::endl;
    }
    bool res = implies(partA, itp);
    if(!res) { return false; }
    if(verbose) {
        std::cout << "; A -> I holds" << std::endl;
    }
    res = implies(itp, logic.mkNot(partB));
    if(!res) { return false; }
    if(verbose) {
        std::cout << "; B -> !I holds" << std::endl;
    }
    return res;
}

