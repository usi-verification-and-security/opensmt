## OpenSMT as a library for your tool

This directory contains examples which may serve as a base for
integrating OpenSMT into an external tool through libraries.

### Compiling

Assuming you've installed OpenSMT headers and libraries under a
directory `<DIR>`, the examples can be compiled by running

    $ cd examples && mkdir build && cd build
    $ cmake -DOPENSMT_DIR=<DIR> ..
    $ make

### Notes

The files serve another purpose: a light-weight regression tests for the
library interface for OpenSMT developers.  Our Travis setup checks that
the compilation passes before a commit is accepted in the master branch.

