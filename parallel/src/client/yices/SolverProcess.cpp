//
// Created by Matteo on 05/09/16.
//

#include <unistd.h>
#include <fcntl.h>
#include <random>
#include <iostream>
#include "client/SolverProcess.h"
#include "yices.h"


//typedef struct lexer_s lexer_t;
//int32_t init_smt2_file_lexer(lexer_t *lex, const char *filename);

const char *SolverProcess::solver = "yices";

void SolverProcess::init() {
    yices_init();
    //init_smt2_file_lexer(NULL, NULL);
}

void SolverProcess::solve() {

}

void SolverProcess::interrupt() {
}