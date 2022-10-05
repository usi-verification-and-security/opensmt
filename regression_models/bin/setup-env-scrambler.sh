#!/bin/bash

if [ $# != 1 ]; then
    echo "Usage: $0 <envdir>"
    exit 1
fi

envdir=$1

mkdir -p ${envdir}
mkdir -p ${envdir}/bin

cd ${envdir}
mkdir -p src;
cd src;
[[ -d scrambler ]] || git clone --single-branch https://github.com/SMT-COMP/scrambler.git
cd scrambler
make;
cp ./scrambler ${envdir}/bin

