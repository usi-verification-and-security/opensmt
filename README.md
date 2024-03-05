[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build Status](https://travis-ci.com/usi-verification-and-security/opensmt.svg?branch=master)](https://travis-ci.com/usi-verification-and-security/opensmt)
[![Gitter](https://badges.gitter.im/usi-verification-and-security/opensmt.svg)](https://gitter.im/usi-verification-and-security/opensmt?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

# OpenSMT2
Copyright 2024 Tomáš Kolárik <tomaqa@gmail.com>  
Copyright 2023 Martin Blicha <martin.blicha@gmail.com>  
Copyright 2019 Antti Hyvarinen <antti.hyvarinen@gmail.com>  
Copyright 2009 Roberto Bruttomesso <roberto.bruttomesso@gmail.com>

Project page: http://verify.inf.usi.ch/opensmt

OpenSMT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

OpenSMT2 is an SMT solver written in C++. It supports reading files in [SMT-LIB2](http://smtlib.cs.uiowa.edu) format and the theories
`QF_UF`, `QF_RDL`, `QF_IDL`, `QF_LRA`, `QF_LIA`, `QF_UFLRA`, `QF_UFLIA` and `QF_AX`.  The system also provides an
API; the distribution includes a minimal example how to use the API.

## Building from source

To build the system from the source code repository, you need a C++17
compliant compiler and the following libraries and headers installed:

 - gmp
 - [libedit](https://thrysoee.dk/editline) (optional)

In addition, the `smtlib2` parser uses `flex` and `bison`.

OpenSMT2 uses CMake as a build system generator.
We use a wrapper `Makefile` (i.e. GNU Make build system) that allows straightforward building and installing of OpenSMT2.

To configure and build the project, run the following command inside the OpenSMT2 directory:
```
$ make
```
This will run `cmake -B <build_dir>` and `cmake --build <build_dir>`.
The default `<build_dir>` is `build`, but it can be changed using the command line option `RELEASE_BUILD_DIR`, for example:
`make RELEASE_BUILD_DIR=build-release`.

If the command is not run for the first time, it only rebuilds the sources that are not up-to-date. In the case the `<build_dir>` was removed, it creates it again.

For better interactive experience from shell, OpenSMT can be linked against the BSD-licensed line-editing library [Editline Library](https://thrysoee.dk/editline).
To do so, run the following instead of the command above:
```
$ make CMAKE_FLAGS=-DENABLE_LINE_EDITING:BOOL=ON
```

The option `CMAKE_FLAGS` may be used for any additional arguments to be passed to `cmake -B <build_dir>`.
Similarly,
the option `CMAKE_BUILD_FLAGS` may be used for any additional arguments to be passed to `cmake --build <build_dir>`.

### Changing build type
The default build type is Release and `make` is in fact just an alias to `make release`.
In order to build in Debug mode, use
```
$ make debug
```
In this case, options that are related to debug build type should use the `*DEBUG*` variants instead of `*RELEASE*`.
For example `DEBUG_BUILD_DIR=<build_dir>`.
The default `<build_dir>` in debug mode is `build-debug`.

In order to build all types, run `make all`.

### Restricting components to build

By default, when building OpenSMT, an executable, a static library, and a shared library are created. However, in certain circumstances, it is desirable not to build components you do not need. In these instances, you *turn off* building components:

- Passing `CMAKE_FLAGS=-DBUILD_STATIC_LIBS:BOOL=OFF` will *turn off* building the static archive for OpenSMT (`libopensmt2.a`)

- Passing `CMAKE_FLAGS=-DBUILD_SHARED_LIBS:BOOL=OFF` will *turn off* building the shared library for OpenSMT (`libopensmt2.so`)

- Passing `CMAKE_FLAGS=-DBUILD_EXECUTABLES:BOOL=OFF` will *turn off* building the OpenSMT executable (`opensmt`)

Given how the `opensmt` executable is built, you cannot build the executable (i.e., with the default value of `-DBUILD_EXECUTABLES:BOOL=ON`) with the static archive *off* (i.e., with `-DBUILD_STATIC_LIBS:BOOL=OFF`).

### Clearing the build

In case one for example needs to rebuild the project from scratch, it can be removed at first:
```
make clean
```
(or `make clean-release`) and then built again with `make` (or `make release`).
In the case of debug mode, one must run `make clean-debug` and `make debug`.
To remove all, run `make clean-all`.

## Unit tests

If you have cmake version 3.11 or higher, the build system will construct unit
tests.  These are available through

```
$ ctest
```

## Installing OpenSMT2
[//]: # "the binary should be placed into `<build_dir>/bin/opensmt`"
As long as you haven't disabled building them, the path to the OpenSMT executable is `<build_dir>/opensmt`, the OpenSMT libraries are located in `<build_dir>/lib`.

To install OpenSMT into your system simply run:
```
$ make install
```
(or `make install-release`).
This runs `cmake --install <build_dir>`.
The install directory can be customized using option `INSTALL_DIR=<install_dir>`.
The default is `/usr/local`.
In such a case, the command above may be neccesary to run with `sudo`.
The default build to be installed is Release. To install the Debug build instead, use `make install-debug`.

The option `INSTALL_DIR` may used with all `make [release|debug]` and `make install[-release|-debug]`.
In the case of the build rules, the `<install_dir>` is configured within the build directory and is used each time `make install[-release|-debug]` is used without the additional option `INSTALL_DIR`.
In the case of the install rules, the `<install_dir>` overrides the previously configured one.

Option `CMAKE_INSTALL_FLAGS` may be used for any additional arguments to be passed to `cmake --install <build_dir>`.

The command installs the executable binary into the folder `<install_dir>/bin`, the library into the folder `<install_dir>/lib` and puts the necessary header files into the folder `<install_dir>/include/opensmt`.

### Examples

Build and install with the default values (assuming that writing into `/usr/local` directory requires root priviledges):
```
make && sudo make install
```

Build Release and install into a local directory `local_dir`:
```
make release INSTALL_DIR=local_dir && make install-release
```

Build Debug and install it into a local directory `local_dir-debug`:
```
make debug INSTALL_DIR=local_dir-debug && make install-debug
```

Build (and configure) with the default values but install into `local_dir`:
```
make && make install INSTALL_DIR=local_dir
```

Build and configure to install into `local_dir` and install there, but also perform another installation into `local_dir2`:
```
make INSTALL_DIR=local_dir && make install && make install INSTALL_DIR=local_dir2
```

## Capabilities and usage examples
OpenSMT is an SMT solver, it decides satisfiability of logical formulas in fragments of first-order logic. The input format is SMT-LIB2 and OpenSMT supports *quantifier-free* SMT-LIB logics, namely any combination of arrays, uninterpreted functions and linear arithmetic or difference logic over reals or integers, both in a single-query and an incremental mode.
The exception is that the combination of reals and integers is not supported.
To streamline upstream usage, OpenSMT supports `ALL` as an argument to `set-logic` command. This is an alias for `QF_AUFLIRA`. Note, however, that while this allows users to specify problems over reals or integers, the restriction that their combination is not allowed still stands!

To run OpenSMT on a SMT-LIB2 file (.smt2) simply pass the path to the file as an argument to the executable:
```
$ opensmt test.smt2
```
It is also possible to run OpenSMT without any arguments, in which case it reads the input from the standard input.

### Other engines

OpenSMT supports multiple SMT solving approaches. By the default it uses CDCL(T) with VSDIS decision heuristic. But it can also utilize Lookahead, possibly with picky heuristic based on VSDIS score. Those engines can be enabled by using following config:
```
(set-option :pure-lookahead true)
```
or
```
(set-option :picky true)
```
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
If you have questions, bug reports, or feature requests, please refer to our [GitHub](https://github.com/usi-verification-and-security/opensmt/issues) issue tracker or send us an email to tomaqa@gmail.com, martin.blicha@gmail.com or antti.hyvarinen@gmail.com.
