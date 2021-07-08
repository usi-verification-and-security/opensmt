## Model validation regression tests

OpenSMT's model validation regression test suite framework runs OpenSMT
on the testsuite with model production enabled and checks the resulting
models for correctness.  The system is based on the infrastructure used in
smt-comp.  The main components are
 - smt-comp `scrambler` used for annotating instances for model production, and
 - smt-comp `ModelValidator`, a python script that uses `pySMT` to check
   whether an input instance conjoined with a model simplifies to
  `true`.

### Setup

The following external packages are needed to set up the environment.
 - `pip3`
 - `cython`

The version of pySMT to be used is give in
`./regression_models/data/requirements.txt`.

The ModelValidator script from smt-comp is included in the repository,
in `./regression_models/data/ModelValidator.py`.

To set up the environment, run `./regression_models/bin/setup_env.sh`.

### Usage

To run the tests, run
`./regression_models/bin/run_tests.sh <path-to-opensmt>`.

