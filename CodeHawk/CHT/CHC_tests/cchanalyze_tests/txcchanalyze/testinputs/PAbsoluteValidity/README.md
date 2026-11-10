# Absolute addresses are not object contracts

The analysis-only source contains unmapped integer-address dereferences. Never
execute these controls. Before the repair, address 1 obtained unconditional
valid-memory, scope, lower-bound and upper-bound discharges merely because it was
a numeric constant. A member access reproduced all four; address -1 also obtained
both bounds. Nonzero does not establish mapped storage or a bounded live object.

The repair removes those statement rules, including the implicit memory-mapped
I/O rules. A platform needing mapped I/O must supply an explicit interface
contract. Nonnull constant facts and separate null diagnostics are retained.
Actual local/global/string objects remain positive controls. Offset expressions
retain their generated base-object obligations; parent arithmetic discharges do
not discharge those premises.

The archive contains parser input only, with no prior proof or invariant reused.
Run `dune runtest CHT/CHC_tests/cchanalyze_tests/txcchanalyze --force`.
