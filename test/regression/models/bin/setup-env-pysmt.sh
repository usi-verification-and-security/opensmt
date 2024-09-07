#!/bin/bash

if [ $# != 2 ]; then
    echo "Usage: $0 <envdir> <datadir>"
    exit 1
fi

envdir=$1
datadir=$2

mkdir -p ${envdir}
mkdir -p ${envdir}/bin

cd ${envdir}
pip3 install -r ${datadir}/requirements.txt
pyinstaller -F ${datadir}/ModelValidator.py
cp dist/ModelValidator ${envdir}/bin

