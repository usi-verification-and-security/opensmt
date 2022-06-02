#!/bin/sh

workdir=$(cd $(dirname $0); pwd)/work

usage="Usage: $0 [-h] <path-to-benchmark>"

while [ $# -gt 0 ]; do
    case $1 in
        -h|--help)
            echo "${usage}"
            exit 1
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

if [ $# -ne 1 ]; then
    echo $usage
    exit 1
fi

if [ ! -x $1 ]; then
    echo "Benchmark $1 is not executable"
fi

current_head=`git rev-parse --short HEAD`
benchmark=$1

mkdir -p $workdir

cp -R lib $workdir/lib-$current_head
cp $benchmark $workdir/$current_head

