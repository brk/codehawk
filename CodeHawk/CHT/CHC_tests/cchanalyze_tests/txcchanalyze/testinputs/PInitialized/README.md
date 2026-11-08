# Byte-copy initialization regression

Run from `CodeHawk/` with `10j opam exec -- dune runtest CHT/CHC_tests -j4`.
The test consumes parser inputs and regenerates UB obligations and invariants;
it does not load cached proof results. Five refinement rounds match the project
analyzer workflow, including discovery of a local copy-count value.

The source fixtures are also included. They were parsed as GCC C99/m64 on an
LP64 host using the CodeHawk-C parser and the unmodified summaries jar already
used by the errno tests. The `.cch.tar.gz` archives contain the parser output.
Unsafe controls are analyzed, never executed.

Seven positive cases cover initialized scalar, union and float copies, a later
source change, initialization on both branches, a complete byte array, and a
local length. Fifteen negative cases cover uninitialized and partially copied
objects, zero copies, narrow union initialization, missing branches/elements,
late initialization/length changes, chains, uncopied fields/tails, overwritten
arrays, and unknown direct/indirect writers. An out-of-bounds copy must still
produce a violation. Uninitialized source-range obligations must stay open.

The implementation uses initialized source facts at the call, not at the later
read, and requires the copied bytes to cover the entire scalar read. It accepts
local scalar/union/array byte ranges whose size and initialization are known;
it does not assume structure padding, arbitrary pointer targets, or unsupported
layout/representation facts. Model-dependent storage and caller preconditions
remain separate obligations. A byte sequence alone is not an initialization
violation: missing copy evidence leaves the result unknown.
