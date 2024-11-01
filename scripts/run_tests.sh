#!/bin/sh

cd ./test/regression
cd base
./run-test-notiming.sh ../../../build/opensmt
cd ../interpolation
./run-tests.sh ../../../build/opensmt
cd ../models
./bin/run-tests.sh ../../../build/opensmt dolmen
cd ../pipe
./run-tests.sh ../../../build/opensmt
cd ../unsatcores
./run-test-notiming.sh ../../../build/opensmt
