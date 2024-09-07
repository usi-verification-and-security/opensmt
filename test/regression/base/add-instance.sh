#!/bin/bash

usage="Usage: $0 [-h] -b <opensmt> [instance [instance [...]]]"

while [ $# -gt 0 ]; do
    case $1 in
        -h|--help)
            echo "${usage}"
            exit 1
            ;;
        -b|--binary)
            osmt=$2
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

if [ -z ${osmt} ]; then
    echo "Error: opensmt not specified.  Use -b <opensmt>"
    exit 1
fi


echo "Adding as follows:"
echo " - osmt: ${osmt} ($(date -r ${osmt}))"
echo " - files: $@"

echo "Is this ok?"
read -p "y/N? "

if [[ ${REPLY} != y ]]; then
    echo "Aborting."
    exit 1
fi

while [ $# -gt 0 ]; do
    echo $1;
    if [[ -a $1 ]]; then
        sh -c "ulimit -St 60; ${osmt} $1 > $1.expected.out 2> $1.expected.err.tmp";
        grep -v '^;' $1.expected.err.tmp > $1.expected.err;
        rm $1.expected.err.tmp
    else
        echo "File does not exist"
    fi;
    shift;
done

