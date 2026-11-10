# Guarded output-region reproducer

`acquire(void **out, size_t n)` has an explicitly trusted file contract:
`return >= 0` implies that `*out` identifies a live, nonnull region of at least
`n` bytes. Its contents are unspecified. Other returns grant no initialization,
region, or preservation. No complete memory frame is installed.

Before the repair, all 33 copied reads were open: output-slot initialization
could not create an origin/capacity for the byte-initialization domain. The
repair captures a distinct immutable output value at each acyclic call site,
then joins its exact return guard, positive literal capacity, covering memset
interval and independent live permission. It grants no disjointness or new
physical object: the allocator may reuse an address. Arbitrary calls invalidate
live permissions; memset never restores permission. A new acquisition creates
a new logical generation. The actual output slot must be a function-scope void*
object; pointer casts do not excuse a narrow/wrong/nested/global slot.

Eight reads become conditional, retaining the complete buffer-on-return
predicate. Twenty-five failure, short, uninitialized, released/recleared/reused,
wrong guard, narrowing, wrong slot, loop, nested, indirect and unsupported reads
remain unknown. Missing/failing return guards also leave raw-slot initialization
open. Existing malloc controls still pass. Unsafe source controls are analyzed,
never executed.

Reproduce with `dune runtest CHT/CHC_tests/cchanalyze_tests/txcchanalyze --force`.
The parser-only archive contains no inferred invariants or proof results.
`guarded_regions.c` and its XML reproduce parsing independently using the
scope-aware CodeHawk-C frontend. Frontend support for predicate tag `bor` is
required to display/reimport the complete guard, output lval and byte capacity.
