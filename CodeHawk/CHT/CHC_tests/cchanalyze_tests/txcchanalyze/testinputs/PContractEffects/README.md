# Explicit call-effect regression

Run the C tests with `10j opam exec -- dune runtest CHT/CHC_tests -j4`
from CodeHawk/. Parser inputs and C source are included. Unsafe controls
are analyzed, never executed.

The contracts deliberately require initialized output slots on entry.
This makes initialized-output guarantees valid on failure paths that do not
write an output. They do not force successful returns. The native test
requires contract-dependent results, and the frontend integration additionally
checks the uninitialized-failure caller retains an unresolved initialized-entry
supporting obligation. A conditional postcondition does not prove that caller
safe without its entry obligations.

Block writes must invalidate old values and initialization. Both writes of a
two-output function must be translated. A postcondition without a complete
write footprint cannot preserve other memory. Initialization derived from
these contracts, including frame facts, must retain model dependencies.

Field postconditions include a full-width union member and a nested structure
field. Both reads must remain conditional on the postcondition. Initializing
one byte of a union cannot initialize a wider member, and a nested field cannot
initialize its sibling. These two negative reads must remain unresolved.
