#!/usr/bin/env bash

RESULTCHECKER=./bin/check_result.py
INSTANCECONSTRUCT=./bin/process-instance.sh
SOLVER=${1}
ok=true

function run_solver () {
    smtfile=$1
    patch=$2
    expected=$3
    TMPDIR=$(mktemp -d)
    inputfile=${TMPDIR}/input.smt2
    ${INSTANCECONSTRUCT} \
        -i ${smtfile} \
        -p ${patch} \
        -o ${inputfile}
    outfile=${TMPDIR}/output.out
    ${SOLVER} ${inputfile} > ${outfile} 2> /dev/null
    if [[ $? != 0 ]]; then
        echo "Error running the solver on ${inputfile} ($smtfile and $patch)"
        ok=false
        return 1
    fi
    ${RESULTCHECKER} ${outfile} ${expected}
    if [[ $? != 0 ]]; then
        echo "Error in result on ${smtfile}"
        ok=false
        return 1
    fi
    rm ${inputfile}
    rm ${outfile}
    rm -rf ${TMPDIR}
    return 0
}

if [[ $# != 1 ]]; then
    echo "Usage: $0 <solver>"
    exit 1
fi

run_solver ./base-instances/NEQ004_size4.smt2.bz2 ./patches/NEQ004_size4_smt2split_0-deep.smt2 unknown
run_solver ./base-instances/NEQ004_size4.smt2.bz2 ./patches/NEQ004_size4_smt2split_0.smt2 unknown
run_solver ./base-instances/init_unsat.smt2.bz2 ./patches/init_unsat-lookahead.smt2 unsat
run_solver ./base-instances/init_unsat.smt2.bz2 ./patches/init_unsat-deep.smt2 unsat
run_solver ./base-instances/iso_brn164.smt2.bz2 ./patches/iso_brn164-deep.smt2 sat
run_solver ./base-instances/iso_brn164.smt2.bz2 ./patches/iso_brn164-lookahead.smt2 sat
run_solver ./base-instances/meti-tarski_sqrt_1mcosq_7_sqrt-1mcosq-7-chunk-0100.smt2.bz2 ./patches/meti-tarski_sqrt_1mcosq_7_sqrt-1mcosq-7-chunk-0100-deep.smt2 sat
run_solver ./base-instances/meti-tarski_sqrt_1mcosq_7_sqrt-1mcosq-7-chunk-0100.smt2.bz2 ./patches/meti-tarski_sqrt_1mcosq_7_sqrt-1mcosq-7-chunk-0100-lookahead.smt2 sat
run_solver ./base-instances/p2-zenonumeric_s6.smt2.bz2 ./patches/p2-zenonumeric_s6-lookahead.smt2 unknown
run_solver ./base-instances/p2-zenonumeric_s6.smt2.bz2 ./patches/p2-zenonumeric_s6-deep.smt2 unknown
run_solver ./base-instances/small.smt2.bz2 ./patches/small-deep.smt2 sat
run_solver ./base-instances/small.smt2.bz2 ./patches/small-lookahead.smt2 sat
run_solver ./base-instances/tta_startup_simple_startup_3nodes.synchro.base.smt2.bz2 ./patches/tta_startup_simple_startup_3nodes.synchro.base-deep.smt2 unsat
run_solver ./base-instances/tta_startup_simple_startup_3nodes.synchro.base.smt2.bz2 ./patches/tta_startup_simple_startup_3nodes.synchro.base-deep.smt2 unsat


if [[ ${ok} == true ]]; then
    exit 0;
else
    exit 1;
fi
