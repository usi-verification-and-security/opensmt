#!/bin/bash

if [ $# != 1 ]; then
    echo "Usage: $0 <path-to-opensmt>"
    exit 1
fi

eval $(opam env)

scriptdir=$(cd $(dirname "$0"); pwd)

${scriptdir}/run-tests.sh $1 dolmen

exit $?
