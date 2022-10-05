#!/bin/bash

scriptdir=$(cd $(dirname $0); pwd)
envdir=${scriptdir}/../env
datadir=${scriptdir}/../data

if [ ! -x $(which opam) ]; then
    echo "Please install opam first: https://opam.ocaml.org/doc/Install.html#Using-your-distribution-39-s-package-system"
    exit 1;
fi

${scriptdir}/setup-env-scrambler.sh $envdir
${scriptdir}/setup-env-dolmen.sh $envdir

mkdir -p $datadir
touch $datadir/ENV-MODERN
