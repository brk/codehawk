# Explicit pointer-validity origins

Analysis-only controls: never execute invalid integer or freed-pointer accesses.
Previously `p=external_pointer(); if(p)*p=7` received an unconditional validity
discharge by IH on receipt, although there was no callee memory contract.
Pointer arguments similarly omitted a caller validity requirement. A no-free
global premise could bypass both missing origins (see PNoFreeValidity).

Require an explicit valid-memory return postcondition, or both new-memory and
heap-address. Preserve the actual postcondition dependencies and every error
alternative: only explicitly null/valid-memory error predicates are accepted by
this conservative rule. An unknown error return, bare new-memory (which may be
stack storage), bare heap classification or readonly frame alone is insufficient.
Nullable malloc remains conditional; null itself satisfies the separate
valid-memory predicate, while nonnull/bounds/alignment are separate checks.

Entry-pointer validity is delegated to the API and creates supporting checks at
callers. Actual local/global objects stay safe. Opaque intervening calls prevent
closure. For a matching free, existing frame-exclusion logic reduces the primary
to a distinct-region supporting obligation; that obligation remains unknown.
The regression checks it explicitly and does not mistake a reduced primary for
a complete lifetime proof.

The two custom summaries in custom-summaries are analysis premises, not claimed
production interfaces. They are stored under return_validity/ in the included
libc summary jar to exercise normal-valid/null-error and normal-valid/unknown-error
returns. File contracts currently reject error-postconditions; the failed import
is retained in campaign evidence. Parser archives contain no inferred results.

Run `dune runtest CHT/CHC_tests -j4 --force`.
