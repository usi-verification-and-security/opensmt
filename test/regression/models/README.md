# Model validation regression tests

OpenSMT's model validation regression test suite runs OpenSMT on model
production enabled and checks the resulting models for correctness.
Currently there are two systems side-by-side, one used in SMT comp and
the other more easily compliable in recent OSs.  The main components are

 - smt-comp `scrambler` used for annotating instances for model
   production, shared by both systems,
 - smt-comp `ModelValidator`, a python script that uses `pySMT` to check
   whether an input instance conjoined with a model simplifies to
  `true`, used in the smt-comp based setup
 - dolmen's model validation (from github), the modern variant

## Setting up

This directory contains scripts for setting up the model validation
environment locally.  If the output produced by the scripts is not
present, the system assumes that the tools are available in the path.

### Setup for smt-comp

The following external packages are needed to set up the smt-comp
environment.
 - `pip3`
 - `cython`

To set up the environment, run
```
./test/regression/models/bin/setup-env-smtcomp.sh
```

The version of pySMT to be used is given in
`./test/regression/models/data/requirements.txt`.

The ModelValidator script from smt-comp is included in the repository,
in `./test/regression/models/data/ModelValidator.py`.

### Setup for dolmen

The following external packages are needed to set up the dolmen
environment.
 - `opam`

To set up the environment, run
```
./test/regression/models/bin/setup-env-dolmen.sh
```


### Usage (smt-comp)

To run the tests, run
```
./test/regression/models/bin/run-tests-smtcomp.sh <path-to-opensmt>
```

### Usage (dolmen)

To run the tests with dolmen, run
```
./test/regression/models/bin/run-tests-dolmen.sh <path-to-opensmt>
```
