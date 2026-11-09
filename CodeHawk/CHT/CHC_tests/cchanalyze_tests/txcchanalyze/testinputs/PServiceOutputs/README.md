Parser-only LP64 service-output controls. Unsafe C is analyzed, never executed.

Regenerate with cCHPOCheckServiceOutputsTest through dune runtest CHT/CHC_tests.
Opaque direct/indirect calls and postcondition-only calls must invalidate copied
scalar initialization and stale index facts; a complete read-only model retains
conditional initialization. Copy output values to unaddressed local state before
an opaque call. Receive failures initialize their pointer slots; RunLoop output
initialization depends on an initialized entry slot, with a negative caller.
