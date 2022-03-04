#!/bin/bash

usage="Usage: $0: [-h] -i <base> -p <patch> -o <output>"

while [ $# -gt 0 ]; do
    case $1 in
        -h|--help)
            echo "$usage"
            exit 1
            ;;
        -i|--intput)
            base=$2
            ;;
        -p|--patch)
            patch=$2
            ;;
        -o|--output)
            output=$2
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
    echo "Basefile not provided or not accessible: $base"
    echo
    echo $usage
    exit 1
fi

if [ -z $patch ] || [ ! -f $patch ]; then
    echo "Patch file not provided or not accessible: $patch"
    echo
    echo $usage
    exit $1
fi

if [ -z $output ]; then
    echo "Outputfile not provided"
    output=/dev/stdout
    echo "Using $output"
fi

uncompressed=${TMPDIR}file.smt2

TMPDIR=$(mktemp -d)
trap "rm -rf ${uncompressed} ${tmpdir}" EXIT

bunzip2 -c $base > $uncompressed
patch $uncompressed -i $patch -o $output > /dev/null

