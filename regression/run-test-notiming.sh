#!/bin/bash
echo "This is the script for running regression tests"
echo " - date: $(date '+%Y-%m-%d at %H:%M.%S')"
echo " - host name $(hostname -f)"
echo " - script path: $(readlink -f $0)"

opensmt=../opensmt
if [[ ! $# -eq 0 ]] ; then
    #echo 'Setting path to' $1
    opensmt=$1
fi

tmpfolder=log-$(date '+%Y-%m-%d-%H-%M-%S')
mkdir ${tmpfolder}

export outmod=false
export errmod=false
export rtmod=false
tolerance=1.5

for file in $(find . -name '*.smt2' |sort) generic/foo; do
    name=$(basename $file)
    dir=$(dirname $file)

    #/usr/bin/time -p -o $tmpfolder/$name.time ${opensmt} $dir/$name > $tmpfolder/$name.out 2>$tmpfolder/$name.err.tmp
    sh -c "ulimit -St 60; ${opensmt} $dir/$name > $tmpfolder/$name.out 2>$tmpfolder/$name.err.tmp" 2>/dev/null 
    #/usr/bin/time -p -o $tmpfolder/$name.time valgrind --leak-check=full ${opensmt} $dir/$name
    #continue
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

