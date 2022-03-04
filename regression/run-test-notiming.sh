#!/bin/bash
get_abs_filename() {
  echo "$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
}

usage="Usage: $0 [-h] <path-to-opensmt>"

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

opensmt=$1

if [ -z ${opensmt} ]; then
    echo "Opensmt binary not specified"
    exit 1
fi

echo "This is the script for running regression tests"
echo " - date: $(date '+%Y-%m-%d at %H:%M.%S')"
echo " - host name $(hostname -f)"
echo " - script path: $(get_abs_filename $0)"

tmpfolder=log-$(date '+%Y-%m-%d-%H-%M-%S')
mkdir ${tmpfolder}

export outmod=false
export errmod=false
export rtmod=false
tolerance=1.5

for file in $(find . -name '*.smt2' |sort) generic/foo; do
    name=$(basename $file)
    dir=$(dirname $file)

    sh -c "ulimit -St 60; ${opensmt} $(echo ${options}) $dir/$name > $tmpfolder/$name.out 2>$tmpfolder/$name.err.tmp" 2>/dev/null

    grep -v '^;' $tmpfolder/$name.err.tmp > $tmpfolder/$name.err
    diff -q ${tmpfolder}/${name}.out ${dir}/${name}.expected.out
    if [ $? != 0 ]; then
        echo "stdout differs for benchmark $file";
        outmod=true;
        diff ${tmpfolder}/${name}.out ${dir}/${name}.expected.out
    fi
    diff -q ${tmpfolder}/${name}.err ${dir}/${name}.expected.err
    if [ $? != 0 ]; then
        echo "stderr differs for benchmark $file";
        errmod=true;
        diff ${tmpfolder}/${name}.err ${dir}/${name}.expected.err
    fi

done
echo "Stdout differs: ${outmod}, stderr differs: ${errmod}"

if [[ ${outmod} == true || ${errmod} == true ]]; then
    echo "There were anomalies: check logs in ${tmpfolder}"
    exit 1
else
    rm -rf ${tmpfolder}
fi

