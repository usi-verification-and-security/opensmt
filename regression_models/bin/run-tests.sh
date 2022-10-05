#!/bin/bash
usage="Usage: $0 <path-to-opensmt> (dolmen | smtcomp)"
if [ $# != 2 ]; then
    echo $usage
    exit 1
fi

opensmt=$1;
mode=$2;

scriptdir=$(cd $(dirname "$0"); pwd)

if [ x"$mode" == x"smtcomp" ]; then
    validatorOpt="-c ${scriptdir}/../env/bin/ModelValidator"
elif [ x"$mode" == x"dolmen" ]; then
    validatorOpt=""
else
    echo "Specify the mode, either dolmen or smtcomp"
    echo $usage
    exit 1
fi

echo "Running model validation tests"

scrambler=${scriptdir}/../env/bin/scrambler

errors=false

for file in ${scriptdir}/../instances/*.smt2; do
    ${scriptdir}/run-and-validate.sh \
        -m ${mode} \
        -o ${opensmt} \
        -s ${scrambler} \
        ${validatorOpt} \
        ${file} || errors=true
done

if [ $errors == "true" ]; then
    exit 1;
fi
