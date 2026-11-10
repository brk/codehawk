# Bounded narrow printf scans

C99 TC3 N1256 7.19.6.1 paragraphs 5 and 8 specify the dynamic precision and
narrow %s scan semantics:
https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf

Before this change, snprintf(dst,16,"%.4s",src) and "%.*s",4,src imposed a
NUL-termination requirement even for a fully initialized four-character array.
The primary obligation generator ignored precision. Positive literals and
representable sizeof/cast precision now generate a finite readable initialized
prefix, without requiring a NUL byte. Keep a valid nonnull character pointer.
The full prefix is a sufficient condition: an earlier NUL could allow less.
Thus failure to prove that stronger prefix is not itself a runtime-UB witness.

19 analysis-only controls cover fixed/dynamic/sizeof precision, independent
field width, multiple conversions, offsets and zero precision. Seven positive
prefix shapes prove. Negative/unknown precision and width-only formats retain
unbounded string obligations. %ls does not use the new byte-prefix rule.
Partial/uninitialized prefixes remain open; oversized/offset scans violate the
bounds predicate; zero precision does not make a NULL %s argument valid.
The pre-existing local NUL tracking limit remains explicit for terminated_good.

Reproduce: dune runtest CHT/CHC_tests/cchanalyze_tests/txcchanalyze --force.
The parser-only archive contains no inferred results. Unsafe controls are never
executed. This repairs input-scan obligations, not snprintf output effects,
full-write guarantees, or wide-character modeling.
