#!/bin/bash

set -e
if [ -d build ]; then rm -rf build; fi
mkdir -p build
cd build

if [ ! -z ${CMAKE_CXX_COMPILER} ]; then
    COMPILER_OPTION="-DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER}"
fi

if [[ $OSTYPE != "darwin"* ]]; then
    LINKER_OPTIONS="-DCMAKE_EXE_LINKER_FLAGS=-static"
fi

cmake -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE} \
      -DCMAKE_CXX_FLAGS="${FLAGS}" \
      -DUSE_READLINE:BOOL=${USE_READLINE} \
      -DENABLE_LINE_EDITING:BOOL=${ENABLE_LINE_EDITING} \
      -DCMAKE_INSTALL_PREFIX=${OSMT_INSTALL} \
      -DMAXIMALLY_STATIC_BINARY=YES\
      -DPACKAGE_BENCHMARKS=${PACKAGE_BENCHMARKS} \
      ${COMPILER_OPTION} \
      ${LINKER_OPTIONS} \
      ..

make -j4

strip opensmt

tar jcf opensmt.tar.bz2 opensmt

echo "Placed stripped, maximally static binary in $(pwd)/opensmt.tar.bz2"
