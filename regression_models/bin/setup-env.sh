#!/bin/bash

scriptdir=$(cd $(dirname $0); pwd)
envdir=${scriptdir}/../env
datadir=${scriptdir}/../data

mkdir -p ${envdir}
mkdir -p ${envdir}/bin
(
    cd ${envdir}
    mkdir -p src;
    cd src;
    [[ -d scrambler ]] || git clone https://github.com/SMT-COMP/scrambler.git
    cd scrambler
    git pull
    make;
    cp ./scrambler ${envdir}/bin
)

(
    cd ${envdir}
    pip3 install -r ${datadir}/requirements.txt
    pyinstaller -F ${datadir}/ModelValidator.py
    cp dist/ModelValidator ${envdir}/bin
)
