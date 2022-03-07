#!/bin/bash
CONSTRUCTSPLIT=./bin/construct-split-instance.sh

usage="Usage: $0 [-h] -i <base> -s <input-dir> -b <solver>"
while [ $# -gt 0 ]; do
    case $1 in
        -h|--help)
            echo "$usage"
            exit 1
            ;;
        -i|--input)
            base=$2
            ;;
        -s|--splits)
            inputs=$2
            ;;
        -b|--binary)
            solver=$2
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

if [ -z $base ] || [ ! -f $base ]; then
    echo "Base file not provided or not accessible: '$base'"
    echo $usage
    exit $1
fi

if [ -z $inputs ] || [ ! -d $inputs ]; then
    echo "Instance directory not provided or not accessible: '$inputs'"
    echo $usage
    exit 1
fi

if [ -z $solver ] || [ ! -f $solver ]; then
    echo "Solver file not provided or not accessible: '$solver'"
    echo $usage
    exit $1
fi

# Note: set to `true' to prevent deletion of temporary files
keep=false
trap "if [ x$keep == xtrue ]; then echo 'keeping output in ${TMPDIR}'; else rm -rf ${TMPDIR}; fi" EXIT

TMPDIR=$(mktemp -d)

numSplits=$(ls $inputs/*.smt2 |wc -l)
if [ $numSplits -eq 0 ]; then
    echo "Error: no splits found"
    exit 1
fi

numSat=0
numUnsat=0

for split in $inputs/*.smt2; do
    $CONSTRUCTSPLIT -i $base -s $split -o $TMPDIR/split.smt2
    splitResult=$($solver $TMPDIR/split.smt2 2>/dev/null)
    if [ x"$splitResult" == x"sat" ]; then
        numSat=$((numSat+1))
    elif [ x"$splitResult" == x"unsat" ]; then
        numUnsat=$((numUnsat+1))
    else
        echo "Unexpected result while solving a split '$TMPDIR/split.smt2': '$splitResult'"
    fi
done

if [ $numUnsat -eq $numSplits ]; then
    echo "unsat"
elif [ $numSat -gt 0 ]; then
    echo "sat"
else
    echo "unknown"
    exit 1
fi


