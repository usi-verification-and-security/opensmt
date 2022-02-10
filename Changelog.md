### 2.2.1 (unreleased)

Performance improvements:
 - Arithmetic: Pooling of `mpq_class` objects for memory reuse.
 - UF: Avoid unnecessary `Enode` instances (negated booleans)
 - UF: Simplified `Enode` representation of terms.

Bug fixes:
 - UF: Fix internal error on top-level distinct in incremental mode.

API changes:
 - Logic: `Logic` now takes SMT-LIB logic type as a constructor parameter to determine which terms it should support.
 - Logic: Support for sorts with arity > 0.
 - Logic: Unification of all arithmetic `Logic`s into a single `ArithLogic`.

Build:
 - The default build does not depend on line editing libraries.

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
