# Simple scripts for benchmarking with visualisation

Our typical use case is that there are two branches that differ in some
intersting way in the implementation of a function.  Google's micro
benchmarking provides a way to write benchmarks for the functionality.
These scripts make it easier to visualise the run time difference in the
two branches.

## Benchmarking

The process consists of three phases.

1. In the fist phase the two branches are compiled and the resulting
   benchmarks are *saved* (see below).
2. In the second phase the two benchmarks are run and a bar chart is
   produced as a `gnuplot` script.
3. Cleanup.  Remove the stored benchmarks.

### Saving the benchmark

`save-benchmark.sh` takes as an argument a path to the benchmark.  It
needs to be run in the build directory (the directory with
`lib/libopensmt.so`).  It copies the benchmark to the directory `work`
in the same directory where the `save-benchmark.sh` script is, along
with `lib/libopensmt.so`, using the name of the current git (short)
commit hash.  It makes therefore sense that the benchmark being saved is
the one compiled in the current commit hash without changes.  For
example:

```
$ cd build
$ git checkout 9ceb3836; make -j4
$ ../benchmarking/save-benchmark.sh benchmark/performance/MakeTermsBenchmarkBig
$ git checkout c64fdd4e; make -j4
$ ../benchmarking/save-benchmark.sh benchmark/performance/MakeTermsBenchmarkBig
```

As a result `../benchmarking/work/` will be populated as follows:

```
$ ls ../benchmarking/work
c64fdd4e 9ceb3836 lib-c64fdd4e lib-9ceb3836
```

### Benchmarking Proper

The benchmarks are run with the script `compare.sh` which uses the
stored benchmarks from the first step.  Continuing the above example,
the usage is

```
$ ../benchmarking/compare.sh 9ceb3836 c64fdd4e |gnuplot > test.png
```

This will place the bar plot in the file `test.png`.

### Cleaning up

The scripts do not remove the directory `../benchmarking/work/`.  To
avoid it growing too big, clean the directory from time to time.

## Notes

For the visualisation to work, it is useful to design the benchmarks so
that there aren't too many sub-tests in a benchmark (say, have only
three per benchmark), and that the sub-test names are not too long.

