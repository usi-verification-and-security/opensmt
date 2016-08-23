#!/usr/bin/env bash

# unsat sat
# unsat unsat
# testing if unsat
# sat == unsat
# unsat
# ./delta/run-both-general.sh: line 21: [[: unsat
# sat: syntax error in expression (error token is "sat")
# This is not the case

# 0 - sat
# 1 - unsat
# 2 - unknown

osmt=/home/hyvaeria/src/opensmt2/opensmt-tmp
z3=/home/hyvaeria/src/z3/bin/external/z3
if [[ $# != 1 ]]; then
    echo "Usage: $0 <file>"
    exit 1
fi

out_osmt=`$osmt $1`
out_z3=`$z3 $1`

if [[ $(echo ${out_osmt} |grep '^\(sat\|unsat\)\( sat\| unsat\)*$') ]];
then
    osmt2_valid=1
else
    osmt2_valid=0
fi

if [[ $(echo ${out_z3} |grep '^\(sat\|unsat\)\( sat\| unsat\)*$') ]];
then
    z3_valid=1
else
    z3_valid=0
fi

#echo ${out_z3}
if [[ ${osmt2_valid} -eq 0 && ${z3_valid} -eq 0 ]]; then
    echo "Both solvers agree on invalidity"
    exit 0
fi

echo "At least one solver considers the input valid"

echo "testing if ${out_osmt} == ${out_z3}"
if [ "${out_osmt}" == "${out_z3}" ]; then
    echo "This is the case"
    exit 0
else
    echo "This is not the case"
    exit 1
fi

