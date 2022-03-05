#!/usr/bin/env bash

INSTANCECONSTRUCT=./bin/process-instance.sh
SPLITSOLVER=./bin/solve-split-instance.sh

# Note: symlinkPath needs to match with the output directory in the instance
symlinkPath=split_and_solve_work

usage="Usage: $0 [-h] -b <solver> -i <input> -p <patch>"

if [ -e $symlinkPath ]; then
    echo "Symbolic link path exists.  Please remove '$symlinkPath'"
    echo "$usage"
    exit 1
fi


TMPDIR=$(mktemp -d)

# Note: set to `true' to prevent deletion of temporary files
keep=false
trap "if [ x$keep == xtrue ]; then echo 'keeping output in ${TMPDIR}'; else rm -rf ${TMPDIR}; fi" EXIT

function constructInstance () {
    smtfile=$1
    patch=$2
    inputfile=${TMPDIR}/input.smt2
    ${INSTANCECONSTRUCT} \
        -i ${smtfile} \
        -p ${patch} \
        -o ${inputfile}
    echo $inputfile
}

while [ $# -gt 0 ]; do
    case $1 in
        -h|--help)
            echo "$usage"
            exit 1
            ;;
        -b|--binary)
            solver=$2
            ;;
        -i|--input)
            base=$2
            ;;
        -p|--patch)
            patch=$2
            ;;
        -*)
            echo "Error: invalid option '$1'"
            exit 1
            ;;
        *)
            break
    esac
    shift; shift
done

if [ -z $solver ] || [ ! -f $solver ]; then
    echo "Solver not provided or does not exist: '$solver'"
    echo $usage
    exit 1
fi

if [ -z $base ] || [ ! -f $base ]; then
    echo "Basefile not provided or not accessible: '$base'"
    echo $usage
    exit 1
fi

if [ -z $patch ] || [ ! -f $patch ]; then
    echo "Patch file not provided or not accessible: '$patch'"
    echo $usage
    exit $1
fi

mkdir $TMPDIR/$symlinkPath
ln -s $TMPDIR/$symlinkPath $symlinkPath

file=$(constructInstance $base $patch)

echo "Running $solver on $file"

solverResult=$($solver $file)

if [ x"$solverResult" != x"unknown" ]; then
    echo $solverResult
fi

numSplits=$(ls $symlinkPath/*.smt2 |wc -l)

if [ $numSplits -eq 0 ]; then
    echo "Error: no splits found but result was unknown"
    exit 1
fi

$SPLITSOLVER -i $base -s $symlinkPath -b $solver

if [ x$keep != xtrue ]; then
    rm $symlinkPath
fi

