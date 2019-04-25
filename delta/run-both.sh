#!/usr/bin/env bash

# 0 - sat
# 1 - unsat
# 2 - unknown

osmt=/Users/prova/src/opensmt2/build/src/bin/opensmt
z3=/Users/prova/src/z3/build/z3
if [[ $# != 1 ]]; then
    echo "Usage: $0 <file>"
    exit 1
fi

out_osmt=`$osmt $1`
echo $out_osmt
res_osmt=2

if [[ $out_osmt == 'sat' ]]; then
    res_osmt=0
elif [[ $out_osmt == 'unsat' ]]; then
    res_osmt=1
fi


out_z3=`$z3 $1`
echo $out_z3
res_z3=2

if [[ $out_z3 == 'sat' ]]; then
    res_z3=0
elif [[ $out_z3 == 'unsat' ]]; then
    res_z3=1
fi

echo "testing if ${res_osmt} == ${res_z3}"
if [[ ${res_osmt} -eq ${res_z3} ]]; then
    echo "This is the case"
    exit 0
else
    echo "This is not the case"
    exit 1
fi
