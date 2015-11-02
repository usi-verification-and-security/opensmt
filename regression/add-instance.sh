#!/usr/bin/env zsh

if [[ $# == 0 ]]; then
    echo "Usage: $0 instance [instance [...]]";
    exit 1.
fi

opensmt=../opensmt

while [[ $# != 0 ]]; do
    echo $1;
    if [[ -a $1 ]]; then
        /usr/bin/time -p -o $1.expected.time ${opensmt} $1 > $1.expected.out 2> $1.expected.err.tmp;
        grep -v '^;' $1.expected.err.tmp > $1.expected.err;
        rm $1.expected.err.tmp
    else
        echo "File does not exist"
    fi;
    shift;
done

