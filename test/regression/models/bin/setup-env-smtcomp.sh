#!/bin/bash

scriptdir=$(cd $(dirname $0); pwd)
envdir=${scriptdir}/../env
datadir=${scriptdir}/../data

${scriptdir}/setup-env-scrambler.sh $envdir
${scriptdir}/setup-env-pysmt.sh $envdir $datadir

mkdir -p $datadir
touch $datadir/ENV-SMTCOMP
