+------------------------------------------------------------------------------+
| OpenSMT2                                                                     |
|                                                                              |
| Copyright 2019 Antti Hyvarinen <antti.hyvarinen@gmail.com>                   |
| Copyright 2009 Roberto Bruttomesso <roberto.bruttomesso@gmail.com>           |
|                                                                              |
| Project page......: http://verify.inf.usi.ch/opensmt                         |
|                                                                              |
| OpenSMT is distributed in the hope that it will be useful,                   |
| but WITHOUT ANY WARRANTY; without even the implied warranty of               |
| MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                         |
+------------------------------------------------------------------------------+

OpenSMT2 supports reading files in `smtlib2` format and the theories
`QF_UF`, `QF_LRA`, `QF_RDL`, and `QF_LIA`.  The system also provides an
api; the distribution includes a minimal example how to use the API.

## Compilation

To compile the system from the source code repository, you need a c++11
compliant compiler and the following libraries and headers installed:

 - gmp
 - readline
 - zlib

In addition the compilation system relies on `cmake` and the `smtlib2`
parser on `flex` and `bison`.  To compile OpenSMT2, use the following
command
```
$ mkdir build; cd build; cmake ..; make
```

## Unit tests

If you have cmake version 3.11, the build system will construct unit
tests.  These are available through

```
$ ./test/unit/LRATest
```

## Using OpenSMT2 interpolation

OpenSMT supports a range of interpolation options for propositional
logic, linear real arithmetic, and uninterpreted functions with
equality.  To enable interpolation code the compilation needs to be
configured by enabling `PRODUCE_PROOF` in the cmake configuration file
`CMakeCache.txt` produced by `cmake` in your build directory.

If you have questions please mail them to me at
antti.hyvarinen@gmail.com, or to the discussion forum!


