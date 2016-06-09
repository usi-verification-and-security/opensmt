#!/usr/bin/env sh
OSMT_INSTALL=/home/hyvaeria/opensmt-install

swig -I${OSMT_INSTALL}/include/opensmt -python -o src/PySMT/opensmt_python_wrap.c src/PySMT/opensmt_python.i
python src/PySMT/setup.py ${OSMT_INSTALL} build

cp build/lib.linux-x86_64-2.7/_opensmt.so examples/
cp src/PySMT/opensmt.py examples/
