#!/bin/bash

set -ev
if [ -d build ]; then rm -rf build; fi
mkdir -p build
cd build

if [ ! -z ${CMAKE_CXX_COMPILER} ]; then
    COMPILER_OPTION="-DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER}"
fi

cmake -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE} \
      -DCMAKE_CXX_FLAGS="${FLAGS}" \
      -DENABLE_LINE_EDITING:BOOL=${ENABLE_LINE_EDITING} \
      -DCMAKE_INSTALL_PREFIX=${OSMT_INSTALL} \
      -DPACKAGE_BENCHMARKS=${PACKAGE_BENCHMARKS} \
      ${COMPILER_OPTION} \
      -DPARALLEL:BOOL=${PARALLEL} \
      ..

make -j4
make test
make install
if [[ ${CMAKE_BUILD_TYPE} == Debug ]]; then
    cd ../regression && ./run-test-notiming.sh ../build/opensmt;
    cd ../regression_itp && ./run-tests.sh ../build/opensmt;
    if [[ "${PARALLEL}" == "ON" ]]; then
      cd ../regression_splitting && ./bin/run-tests.sh ../build/opensmt-splitter;
    fi
    cd ../regression_pipe && ./run-tests.sh ../build/opensmt;
    cd ../regression_models
    if [[ x"${MODEL_VALIDATION}" == x"Dolmen" || -f ./data/ENV-MODERN ]]; then
        ./bin/run-tests-dolmen.sh ../build/opensmt;
    elif [[ x"${MODEL_VALIDATION}" == x"pySMT" || -f ./data/ENV-SMTCOMP ]]; then
        ./bin/run-tests-smtcomp.sh ../build/opensmt;
    else
        echo "Error: the model regression environment is not set."
        exit 1
    fi
fi

cd ../examples && rm -rf build && mkdir -p build && cd build
cmake \
    -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE} \
    -DCMAKE_CXX_FLAGS="${FLAGS}" \
    -DOpenSMT_DIR=${OSMT_INSTALL} \
    ..

make -j4
