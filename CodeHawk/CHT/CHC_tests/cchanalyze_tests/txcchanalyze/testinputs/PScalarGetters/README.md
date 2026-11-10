# Read-only integer field getters

The exact complete-readonly contract `return == d->capacity` did not transport
an integer metadata field. Thus `d.capacity=8; memset(image,0,get_capacity(&d))`
left a four-byte copied read open although the corresponding direct-field and
pointer-field getter shapes were supported. The same issue occurs with native
CFE_TBL_LoadBuffGetAllocSize and a 4928-byte WDT.

Transport only ordinary nonvolatile integer fields of the exact return kind,
through scope-certified eligible descriptors whose address is exposed solely
to modeled complete-readonly field getters. Pointers retain the existing policy.
Exclude Boolean/float/enum/narrowing reinterpretations, union, nested, escaped,
opaque and partial-frame metadata. Capture the value at call time; a later field
assignment does not retarget the result. All safe caller checks retain the exact
field-equality postcondition and readonly frame; own entry premises are excluded
from that call's postconditions.

Three reduced reads become conditional and twelve negative/unsupported controls
remain open. Missing capacity metadata remains an open call entry requirement.
A capacity field value creates no pointer region, payload initialization or
allocation ownership. Zero and short clears cannot initialize a wider read.
The real-type WDT clear becomes conditional. The combined pooled pointer/size
getter shape is retained separately as an unresolved transport boundary.

Reproduce: dune runtest CHT/CHC_tests/cchanalyze_tests/txcchanalyze --force.
C/XML/parser-only inputs are included; unsafe source cases are never executed.
