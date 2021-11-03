[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build Status](https://travis-ci.com/usi-verification-and-security/opensmt.svg?branch=master)](https://travis-ci.com/usi-verification-and-security/opensmt)
[![Gitter](https://badges.gitter.im/usi-verification-and-security/opensmt.svg)](https://gitter.im/usi-verification-and-security/opensmt?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

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

To build the system from the source code repository, you need a C++17
compliant compiler and the following libraries and headers installed:

 - gmp
 - libedit or readline (optional)

In addition the `smtlib2` parser uses `flex` and `bison`.
OpenSMT2 uses `cmake` as a build system generator. To compile OpenSMT2 (using `make` build system), use the following
command
```
$ mkdir build; cd build; cmake ..; make
```

For better interactive experience from shell, OpenSMT can be linked against the BSD-licensed line-editing library [Editline Library](https://thrysoee.dk/editline/). You can optionally choose to build OpenSMT against the GPL-licensed [GNU Readline Library](https://tiswww.case.edu/php/chet/readline/rltop.html). Building OpenSMT in this way means that the resulting binary is GPL licensed, and not MIT licensed. To enable line editing with editline:
```
$ cmake -DENABLE_LINE_EDITING:BOOL=ON ..
```

and to enable `readline` and create a GPL-licensed build of OpenSMT:
```
$ cmake -DENABLE_LINE_EDITING:BOOL=ON -DUSE_READLINE:BOOL=ON ..
```

### Changing build type
The default build type is RELEASE. Different build type can be configured using cmake variable CMAKE_BUILD_TYPE. For example, to create a debug build use
```
$ cmake -DCMAKE_BUILD_TYPE=Debug ..
```

### Restricting components to build

By default, when building OpenSMT, an executable, a static library, and a shared library are created. However, in certain circumstances, it is desirable not to build components you do not need. In these instances, you *turn off* building components:

- Passing `-DBUILD_STATIC_LIBS:BOOL=OFF` will *turn off* building the static archive for OpenSMT (`libopensmt2.a`)

- Passing `-DBUILD_SHARED_LIBS:BOOL=OFF` will *turn off* building the shared library for OpenSMT (`libopensmt2.so`)

- Passing `-DBUILD_EXECUTABLES:BOOL=OFF` will *turn off* building the OpenSMT executable (`opensmt`)

Given how the `opensmt` executable is built, you cannot build the executable (i.e., with the default value of `-DBUILD_EXECUTABLES:BOOL=ON`) with the static archive *off* (i.e., with `-DBUILD_STATIC_LIBS:BOOL=OFF`).


## Unit tests

If you have cmake version 3.11 or higher, the build system will construct unit
tests.  These are available through

```
$ ctest
```

## Installing OpenSMT2
As long as you haven't disabled building them, the path to the OpenSMT executable is `<BUILD_DIR>/src/bin/opensmt`, the OpenSMT libraries are located in `<BUILD_DIR>/src/api`.
To install OpenSMT in your system simply run
```
$ make install
```
The install directory can be customized using cmake variable CMAKE_INSTALL_PREFIX. The default is `/usr/local`.
This installs the library in the folder `<INSTALL_DIR>/lib` and puts the necessary header files in the folder `<INSTALL_DIR>/include/opensmt`.

## Capabilities and usage examples
OpenSMT is an SMT solver, it decides satisfiability of logical formulas in fragments of first-order logic. The input format is SMT-LIB2 and OpenSMT currently supports the following SMT-LIB logics: `QF_UF`, `QF_LRA`, `QF_RDL`, `QF_IDL`, and `QF_LIA`, both in a single-query and an incremental mode.

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

Interpolation is supported for SMT-LIB logics `QF_UF`, `QF_LRA`, and `QF_LIA` in both single-query and incremental mode. An example of how SMT-LIB2 file can be extended to instruct OpenSMT to compute interpolants can be found [here](regression_itp/itp_bug_small.smt2).

## Contact
If you have questions please mail them to me at antti.hyvarinen@gmail.com, or at [github](https://github.com/usi-verification-and-security/opensmt)


