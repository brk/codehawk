The source and parser input mirror LC's byte loop. This conditional summary
requires 1 <= N <= 4, N readable/initialized source bytes, four initialized
map bytes each strictly below N, and a pre-initialized full destination word. Destination and map must not overlap, preserving the map
throughout the copy.
The exact write footprint is N bytes. Requiring all four unmasked map bytes
below N is stronger than the minimal loop condition but admits the actual
16-bit and 32-bit conversion maps without an extra two source bytes.

Native tests regenerate conditional destination-output proofs; they do not
claim caller entry requirements are proved. Full frontend integration must
check those supporting obligations separately: the two- and four-byte local
positive callers have 18 discharged requirements each. Invalid first/second
indices, a truncated or uninitialized source, an uninitialized destination
tail, an unknown map writer, and an unsigned-byte cast of -1 each retain open
or violated requirements. observe_map has an explicit empty write footprint;
map bounds preserved across that call must retain its contract dependency.

The field-value checker uses only exact nonnegative integer facts from the
matching field/element, with a nonnegative value-preserving constant bound.
It must not use a sibling field, an unknown writer's stale value, or ignore
C signed/unsigned conversion behavior. Unsafe C controls are analyzed only.
