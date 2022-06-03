#!/bin/bash

workdir=$(cd $(dirname $0); pwd)/work

usage="Usage: $0 [-h] <hash1> <hash2>"

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

if [ $# != 2 ]; then
    echo ${usage}
    exit 1
fi

benchmark1=$workdir/$1
benchmark2=$workdir/$2

lib1=$workdir/lib-$(basename $benchmark1)
lib2=$workdir/lib-$(basename $benchmark2)

if [ ! -x $benchmark1 ]; then
    echo "Not executable: $benchmark1"
    exit 1;
fi

if [ ! -x $benchmark2 ]; then
    echo "Not executable: $benchmark2"
    exit 1;
fi

if [ ! -d $lib1 ]; then
    echo "library directory not found: $lib1"
    exit 1;
fi

if [ ! -d $lib2 ]; then
    echo "library directory not found: $lib2"
    exit 1;
fi

TMPDIR=$(mktemp -d)
trap "rm -rf ${TMPDIR}" EXIT

tests=`LD_LIBRARY_PATH=$lib1 $benchmark1 --benchmark_list_tests`

echo "Running benchmark $benchmark1 three times and saving the last" >&2
for ((j=0; j < 3; j++)); do
    LD_LIBRARY_PATH=$lib1 $benchmark1 --benchmark_format=csv \
        |csvcut -c 'name,real_time' > $TMPDIR/bm1.csv
done

echo "Running benchmark $benchmark2 three times and saving the last" >&2
for ((i=0; i < 3; i++)); do
    LD_LIBRARY_PATH=$lib2 $benchmark2 --benchmark_format=csv \
        |csvcut -c 'name,real_time' > $TMPDIR/bm2.csv
done

echo "set term pngcairo color"

echo -n "set xtics ("
offset=0
for test in $tests; do
    echo -n "\"$test\" $(echo "$offset+0.25" | bc -l), "
    offset=$(echo "$offset+1.5" | bc -l)
done
echo ")"

echo set yrange [0:]
echo set boxwidth 0.5
echo set style fill solid
echo "plot '-' using 1:2 with boxes ls 1 title '$(basename $benchmark1)', '-' using 1:2 with boxes ls 2 title '$(basename $benchmark2)'"

offset=0
for test in $tests; do
    bm1res=$(csvgrep -m $test -c name $TMPDIR/bm1.csv |csvcut -c real_time |tail -1)
    bm2res=$(csvgrep -m $test -c name $TMPDIR/bm2.csv |csvcut -c real_time |tail -1)
    echo $offset $bm1res
    offset=$(echo $offset + 1.5 |bc -l)
done
echo e

offset=0
for test in $tests; do
    bm2res=$(csvgrep -m $test -c name $TMPDIR/bm2.csv |csvcut -c real_time |tail -1)
    echo $(echo $offset+0.5 |bc -l) $bm2res
    offset=$(echo $offset + 1.5 |bc -l)
done
