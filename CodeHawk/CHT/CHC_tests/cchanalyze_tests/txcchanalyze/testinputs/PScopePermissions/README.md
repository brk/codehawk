These C functions are analysis-only controls; never execute the invalid cases.
The parser archive contains only parser inputs, not inferred proofs/invariants.

`PScopePermissionsLegacy/scope_legacy.cch.tar.gz` contains the same input
with `iattrs` removed from each function's `sbody` XML node. This removes the
versioned parser scope certificate and checks that older parser output cannot
silently certify a stack object's lifetime. Static/global objects retain their
storage-duration evidence independently of that certificate. Paths use a
different basename so both controls can run concurrently without sharing output.

Reproduce with `dune runtest CHT/CHC_tests -j4 --force` from `CodeHawk` in the
provided OPAM environment. Live nested aliases deliberately remain open:
declaration-to-use lexical scope mapping is not represented yet.
