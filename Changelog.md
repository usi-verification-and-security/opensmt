### 2.8.0 (unreleased)

API changes:
 - Enclosed the whole project into `opensmt` namespace.
 - Using also directory names when including files.

Bug fixes:
 - Named terms: do not report error when re-introducing a named term with an already popped name.

New features:
 - Support ":minimal-unsat-cores" option - naive implementation of subset-minimal unsat cores.
 - Support ":print-cores-full" option - make the unsat cores strictly agnostic to the ":named" terms.

Build:
 - Switch to C++20.
 - Bumped minimal CMake version to 3.14.

Other:
 - Refactored regression and unit tests.

### 2.7.0 (2024-05-29)

Bug fixes:
 - Fix unsoundness in incremental solving involving theory combination (introduced in 2.6.0).
 - Fix unsoundness in handling nested arrays.
 - Fix bug in one of the constructors of FastRational.

New features:
 - Experimental support for unsat cores.

### 2.6.0 (2024-03-06)

New features:
 - Support `ALL` as a valid argument to `set-logic` command. This becomes an alias for `QF_AUFLIRA`.
 - Simpler builds with single `make` command.

API changes:
 - Various small fixes for compatibility with JavaSMT and C++20.

Removed features:
 - Dropped support for `readline` library.

Performance improvements:
 - Faster preprocessing in incremental solving.

### 2.5.2 (2023-07-12)

Bug fixes:
 - ArithLogic: Fix corner cases for div and mod operators

### 2.5.1 (2023-05-23)

Bug fixes:
 - SMT-LIB frontend: Fix spurious error when a formal argument in define-fun command had the same name, but different sort than a declared variable
 - SMT-LIB fronted: Fix response to get-value command
 - Preprocessing: Fix infinite cycle in computation of substitutions

### 2.5.0 (2023-03-27)

Bug fixes:
 - QF_AX: Fix unsoundness bug due to missing literals in read-over-weak-eq lemmas

API changes:
 - Pterms: Change operator < on PTRefs to more intuitive implementation 

New features:
 - Implemented the interpolant production and incrementality for the Lookahead
 - Support for the combination of arrays and linear arithmetic (QF_ALIA, QF_AUFLIA)
 - Implemented new solving heuristic - Picky CDCL, as an extension for the lookahead

### 2.4.3 (2022-11-21)

Bug fixes:
 - UFLA: Fix unsoundness bug due to LASolver not signalling the presence of conflict correctly
 - ArithLogic: Fix substitution computation in the presence of uninterpreted functions
 - Logic: Evaluate `distinct` function on constant arguments (required for model evaluation)

### 2.4.2 (2022-10-24)

Bug fixes:
 - TSolverHandler: Remove dependency on the global objects initialization order
 - ScatterSplitter: Fix the implementation of scattering

Performance improvements:
 - ArithLogic: Improved computation of substitutions from equalities
 - ScatterSplitter: Limit sizes of shared literal representations

New features:
 - The shared clause representation is now portable between solvers for
   all terms

Build:
 - Support for Apple M1

### 2.4.1 (2022-07-28)

Bug fixes:
 - Logic: Fix use of uninitialized value

### 2.4.0 (2022-07-22)

Bug fixes:
 - Fix handling of scoped `define-fun`s in incremental mode

Performance improvements:
 - CoreSMTSolver: Use Luby restart scheme
 - CoreSMTSolver: Sticky polarities with phase flipping
 - CoreSMTSolver: Do not delete learned clauses with glue score < 4

New features:
 - A library for use in parallel SMT solving
 - Support for the theory of arrays with extensionality (QF_AX)

### 2.3.2 (2022-04-20)

Bug fixes:
 - STP: Fix crash on problems with no theory variables
 - UF+Interpolation: Fix bug in congruence graph coloring

Build:
 - Support building statically linked executable

### 2.3.1 (2022-03-16)

Bug fixes:
 - Fix crash on non-standard SMT-LIB scripts

Various improvements:
 - Small performance improvements for Arithmetic theories
 - Small performance improvements for preprocessing

Build:
 - Fix version number in CMake files

### 2.3.0 (2022-03-09)

Performance improvements:
 - Arithmetic: Pooling of `mpq_class` objects for memory reuse.
 - UF: Avoid unnecessary `Enode` instances (negated booleans)
 - UF: Simplified `Enode` representation of terms.
 - Integer arithmetic: Support of cuts-from-proofs algorithm to better avoid divergence.

Bug fixes:
 - UF: Fix internal error on top-level distinct in incremental mode.
 - LIA+Interpolation: Fix interpolation in incremental mode when split clauses are involved.
 - UF+Interpolation: Fix interpolation in the presence of `distinct`s.
 - Logic+Parser: Fix handling of (unusual) quoted identifiers.
 - Logic+Parser: Fix handling of qualified terms (operator `as`).

API changes:
 - Logic: `Logic` now takes SMT-LIB logic type as a constructor parameter to determine which terms it should support.
 - Logic: Support for sorts with arity > 0.
 - Logic: Unification of all arithmetic `Logic`s into a single `ArithLogic`.

New features:
- Support for theory combination: QF_UFLRA, QF_UFLIA.

Build:
 - The default build does not depend on line editing libraries.

 Various improvements:
 - Fix several memory leaks mostly related to string manipulation.

### 2.2.0 (2021-10-04)

API changes:
 - LA: Inequalities with multiple arguments are now handled according to SMT-LIB standard.
 - Logic: Refactoring of methods for term creation (added overloads for taking arguments as r-value reference). 

Bug fixes:
 - LA: Fix bound store not being cleared properly between consecutive `(check-sat)` commands.
 - LA: Fix incorrect update of bounds after split.

Build:
 - Switch to C++17.

Various improvements:
 - Interpolation mode now also uses theory propagation.
 - LA: Arithmetic equalities are now normalized in the same way as inequalities are.


### 2.1.0 (2021-08-16)

API changes:

 - Single `Logic` can now be used by multiple `MainSolver`s.
 - `MainSolver`, when provied with a `Logic`, is now responsible for all
   other compenents in the solver.
 - Standalone `Model` object can now be obtained from `MainSolver` in sat
   state using `MainSolver::getModel`. This model object can be queried for
   value of various terms.
 - Interpolants are now computed using a standalone `InterpolationContext`
   object that can be obtained from `MainSolver` using
   `MainSolver::getInterpolationContext`.
 - Methods for term rewriting has been moved to separate classes. This
   includes term substitution and rewriting of mod/div operations or
   distinct terms.
 - Support for parallel / distributed solving with `SMTS` is removed for
   this release, but is being currently developed in a different branch.

Various improvements:

 - Parser: Improved processing of nested let terms.
 - Terms: Better processing of ITE terms.
 - LIA: Inequalities are strengthened when created in `LIALogic`.
 - LIA: Various performance improvements through better memory usage
 - LIA: Added support for interpolation in `QF_LIA`.
 - LIA: Allow the use of div and mod in the api and through an option in
   smtlib2 files
 - SMT-LIB: The output of `(get-interpolants)` command now conforms to the interpolation proposal.
 - Data structures: Added `MapWithKeys` that supports easy and efficient iteration over map's keys.
 - SMT-LIB: Added dedicated solvers for `QF_RDL` and `QF_IDL`.
 - Models: Enable producing models in `QF_UF`.
 - Interpolation: Determinising theory interpolation

Bug fixes:

 - `FastRationals`: Fixed undefined behaviour in `FastRational::absVal`
 - `FastRationals`: Fixed overflow in subtraction.
 - `FastRationals`: Faster implementations for operators
 - UF: Fixed various issues with handling boolean terms inside
   uninterpreted functions.
 - Interpret: Support correctly push and pop commands with integer
   argument.
 - Interpret: Standard-compliant handling of `declare-const`
 - Interpret: fix the methods for unbuffered reading from pipe
 - Data structures: Do not use `mtl::vec` when the stored type is not trivially copyable.
 - Fixed handling of distinct that are not on the top level of the input formula.
 - Interpolating mode: Fixed incremental solving with empty frames.

Build:

 - `OpenSMT`'s executable is now created directly in the build directory.
 - `OpenSMT`'s libraries are created in lib subdirectory of the build directory.
 - `OpenSMT` now provides and installs `CMake` package for easier
   integration in projects using `CMake`.
