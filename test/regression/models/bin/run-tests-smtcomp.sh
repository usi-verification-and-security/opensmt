#!/bin/bash

if [ $# != 1 ]; then
    echo "Usage: $0 <path-to-opensmt>"
    exit 1
fi

scriptdir=$(cd $(dirname "$0"); pwd)

${scriptdir}/run-tests.sh $1 smtcomp

exit $?
