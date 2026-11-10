# Nullable normal-return aliases

The supplied fgets summary has `normal: return == s && return != NULL` and
`error: return == NULL`. The numeric call translator applied the normal alias
also when that error alternative was present. `p=fgets(buffer,8,stream); *p`
was incorrectly proved nonnull from buffer's stack address. The same false proof
survived an unrelated nonnull-pointer guard. A valid FILE can already be at EOF;
the cFS native witness demonstrates that case without dereferencing NULL.

Do not transport normal return values/aliases when error alternatives exist.
Keep the immutable call result and existing conservative postcondition branches.
The valueset translator already follows this policy; ordinary memcpy/memset
normal-only aliases remain supported. No new successful-return or failure-frame
assumption is added. The unchecked and unrelated-guard nonnull proofs reopen.
The explicitly failed branch stays open. The safe guarded-fgets control also
stays open: its simple null-guard precision is a separately demonstrated limit,
not a reason to retain the false normal-alias proof.

Reproduce: dune runtest CHT/CHC_tests/cchanalyze_tests/txcchanalyze --force.
The source and parser-only archive are standalone; the existing test summary jar
contains fgets. Unsafe examples are analyzed only. The native valid-stream
EOF/success witness is in the cFS campaign, where all eight checks pass.
