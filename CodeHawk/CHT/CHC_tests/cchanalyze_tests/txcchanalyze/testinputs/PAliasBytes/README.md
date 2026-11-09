Parser-only LP64 local alias/descriptor byte controls. Unsafe C is never run.

Only exact numeric local-address values of unaddressed local pointer/structure
slots are accepted. Globals, escaped slots, union views, pointer/integer casts,
explicit global-value contracts, ambiguous regions and numeric pointer arithmetic
remain unsupported. Pointer offsets are calculated from the original C pointer
type, including IndexPI; backing extents remain those of the declared object.

Aliased memset seeds the existing exact local interval. Source aliases and
captured descriptor lengths use facts from the memcpy call, not a later read.
Model identity/frame facts remain conditional. Same-object and unresolved alias
writes, opaque/indirect calls and release discard intervals; even disjoint alias
writes may lose precision. Allocator results and external callback regions do
not become initialized local objects.

35 controls retain twelve discharged local positives, two conditional model
positives, and 21 open negative/unsupported cases. Reduced Entry is not the
production WDT type and changes no production capacity. A separate actual-size
native TBL/LC harness and fresh production inventories are captured in cFS.
