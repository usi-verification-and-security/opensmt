#!/usr/bin/env bash

RESULTCHECKER=./bin/check_result.py
SOLVER=${1}
ok=true

function run_solver () {
    smtfile=$1
    expected=$2
    outfile=$(mktemp -t $(basename ${smtfile}.XXXXXX))
    ${SOLVER} ${smtfile} > ${outfile} 2> /dev/null
    if [[ $? != 0 ]]; then
        echo "Error running the solver on ${smtfile}"
        ok=false
        return 1
    fi
    ${RESULTCHECKER} ${outfile} ${expected}
    if [[ $? != 0 ]]; then
        echo "Error in result on ${smtfile}"
        ok=false
        return 1
    fi
    rm ${outfile}
    return 0
}

if [[ $# != 1 ]]; then
    echo "Usage: $0 <solver>"
    exit 1
fi

run_solver ./instances/NEQ004_size4_smt2split_0-deep.smt2 unknown
run_solver ./instances/NEQ004_size4_smt2split_0.smt2 unknown
run_solver ./instances/init_unsat-deep.smt2 unsat
run_solver ./instances/init_unsat.smt2 unsat
#run_solver ./instances/iso_brn164-deep.smt2 sat
#run_solver ./instances/iso_brn164.smt2 sat
run_solver ./instances/meti-tarski_sqrt_1mcosq_7_sqrt-1mcosq-7-chunk-0100-deep.smt2 sat
run_solver ./instances/meti-tarski_sqrt_1mcosq_7_sqrt-1mcosq-7-chunk-0100.smt2 sat
#run_solver ./instances/p2-zenonumeric_s6-deep.smt2 unknown
#run_solver ./instances/p2-zenonumeric_s6.smt2 unknown
run_solver ./instances/small-deep.smt2 sat
run_solver ./instances/small.smt2 sat
run_solver ./instances/tta_startup_simple_startup_3nodes.synchro.base-deep.smt2 unsat
run_solver ./instances/tta_startup_simple_startup_3nodes.synchro.base.smt2 unsat

if [[ ${ok} == true ]]; then
    exit 0;
else
    exit 1;
fi
