[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build Status](https://travis-ci.com/usi-verification-and-security/opensmt.svg?branch=master)](https://travis-ci.com/usi-verification-and-security/opensmt)

# OpenSMT2
Copyright 2019 Antti Hyvarinen <antti.hyvarinen@gmail.com>  
Copyright 2009 Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

Project page: http://verify.inf.usi.ch/opensmt

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

OpenSMT2 is an SMT solver written in C++. It supports reading files in [SMT-LIB2](http://smtlib.cs.uiowa.edu) format and the theories
`QF_UF`, `QF_LRA`, `QF_RDL`, and `QF_LIA`.  The system also provides an
API; the distribution includes a minimal example how to use the API.

## Building from source

To build the system from the source code repository, you need a C++11
compliant compiler and the following libraries and headers installed:

 - gmp
 - readline

In addition the `smtlib2` parser uses `flex` and `bison`.
OpenSMT2 uses `cmake` as a build system generator. To compile OpenSMT2 (using `make` build system), use the following
command
```
$ mkdir build; cd build; cmake ..; make
```

### Changing build type
The default build type is RELEASE. Different build type can be configured using cmake variable CMAKE_BUILD_TYPE. For example, to create a debug build use
```
$ cmake -DCMAKE_BUILD_TYPE=Debug ..
```


## Unit tests

If you have cmake version 3.11 or higher, the build system will construct unit
tests.  These are available through

```
$ ctest
```

## Installing OpenSMT2
After a successful build, an executable, a static library, and a shared library are created.
The path to the executable is `<BUILD_DIR>/src/bin/opensmt`, the libraries are located in `<BUILD_DIR>/src/api`.
To install OpenSMT in your system simply run
```
$ make install
```
The install directory can be customized using cmake variable CMAKE_INSTALL_PREFIX. The default is `/usr/local`.
This installs the library in the folder `<INSTALL_DIR>/lib` and puts the necessary header files in the folder `<INSTALL_DIR>/include/opensmt`.

## Capabilities and usage examples
OpenSMT is an SMT solver, it decides satisfiability of logical formulas in fragments of first-order logic. The input format is SMT-LIB2 and OpenSMT currently supports the following SMT-LIB logics: `QF_UF`, `QF_LRA`, `QF_RDL`, and `QF_LIA`, both in a single-query and an incremental mode.
Note however that the incremental mode for QF_LIA has not been thoroughly tested yet.

To run OpenSMT on a SMT-LIB2 file (.smt2) simply pass the path to the file as an argument to the executable:
```
$ opensmt test.smt2
```
It is also possible to run OpenSMT without any arguments, in which case it reads the input from the standard input.

### Interpolation
OpenSMT supports a range of interpolation algorithms for propositional
logic, linear real arithmetic, and uninterpreted functions with
equality.

When using OpenSMT as an executable, interpolation is off by default. It can be enabled by passing `-i` option to the executable, or by setting the SMT-LIB option `produce-interpolants` in the input file **before** the `(set-logic)` command.
```
(set-option :produce-interpolants 1)
```

When using OpenSMT as a library, the option needs to be set in `SMTConfig` **before** `Opensmt` object is created, see [this example](examples/test_lra_itp.cc).

Interpolation is supported for SMT-LIB logics `QF_UF` and `QF_LRA` in both single-query and incremental mode. An example of how SMT-LIB2 file can be extended to instruct OpenSMT to compute interpolants can be found [here](regression_itp/itp_bug_small.smt2).

## Contact
If you have questions please mail them to me at
antti.hyvarinen@gmail.com, or to the discussion forum!


