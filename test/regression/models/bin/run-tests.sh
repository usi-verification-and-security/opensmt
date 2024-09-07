#!/bin/bash
usage="Usage: $0 <path-to-opensmt> (dolmen | smtcomp)"
if [ $# != 2 ]; then
    echo $usage
    exit 1
fi

opensmt=$1;
mode=$2;

scriptdir=$(cd $(dirname "$0"); pwd)

echo "Locating tools for model validation"

if ! [ -x "${opensmt}" ]; then
    echo "Opensmt ${opensmt} is not usable"
    exit 1
fi

if [ x"$mode" == x"smtcomp" ]; then
    if [ -x "${scriptdir}/../env/bin/ModelValidator" ]; then
        modelvalidator="${scriptdir}/../env/bin/ModelValidator"
    elif [ -x "$(command -v ModelValidator)" ]; then
        modelvalidator="$(command -v ModelValidator)"
    else
        echo "Could not find usable ModelValidator"
        exit 1
    fi
elif [ x"$mode" == x"dolmen" ]; then
    if [ -x "${scriptdir}/../env/bin/dolmen" ]; then
        modelvalidator="${scriptdir}/../env/bin/dolmen"
    elif [ -x "$(command -v dolmen)" ]; then
        modelvalidator="$(command -v dolmen)"
    else
        echo "Could not find usable dolmen"
        exit 1
    fi
else
    echo "Specify the mode, either dolmen or smtcomp"
    echo $usage
    exit 1
fi

# Model validator found
echo "Using model validator $modelvalidator"

if [ -x ${scriptdir}/../env/bin/scrambler ]; then
    scrambler=${scriptdir}/../env/bin/scrambler
elif [ -x "$(command -v scrambler)" ]; then
    scrambler=$(command -v scrambler);
else
    echo "Could not find usable scrambler"
    exit 1
fi

# Scrambler is found
echo "Using scrambler $scrambler"

echo "Running model validation tests"

errors=false

for file in ${scriptdir}/../instances/*.smt2; do
    ${scriptdir}/run-and-validate.sh \
        -m ${mode} \
        -o ${opensmt} \
        -s ${scrambler} \
        -c ${modelvalidator} \
        ${file} || errors=true
done

if [ $errors == "true" ]; then
    exit 1;
fi
