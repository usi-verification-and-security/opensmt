#!/bin/bash

if [ $# != 1 ]; then
    echo "Usage: $0 <envdir>"
    exit 1
fi

envdir=$1
datadir=$2

mkdir -p ${envdir}
mkdir -p ${envdir}/bin

if [ ! -x $(which opam) ]; then
    echo "Please install opam first: https://opam.ocaml.org/doc/Install.html#Using-your-distribution-39-s-package-system"
    exit 1;
fi

mkdir -p ${envdir}
mkdir -p ${envdir}/bin

cd ${envdir}
[[ -d dolmen ]] || git clone --single-branch https://github.com/Gbury/dolmen.git
cd dolmen
opam pin add -y .
opam install -y --deps-only .
make

