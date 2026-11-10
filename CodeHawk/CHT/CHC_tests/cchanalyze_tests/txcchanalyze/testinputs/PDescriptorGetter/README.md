# Read-only descriptor getter transport

`descriptor_getter.c` is analysis-only C, including unsafe cases. The XML
describes a getter returning `descriptor->pointer`, with a complete read-only
footprint and an initialized pointer-field entry requirement. It supplies no
payload bytes, capacity, nonnull guarantee, allocation or lifetime.

Before the repair, the three getter copy positives remained unknown even with
this contract. The direct local-array equivalent discharged. Numeric call
translation understood `return == argument`, but ignored an addressed field.

The repair resolves pointer-field return equalities only for certified
function-scope ordinary local descriptors. Their addresses may be exposed
solely to complete read-only getters returning a pointer field. Root-alias
returns, opaque exposure, partial metadata access, union views, volatile
metadata, nested scope, loops and pointer/integer conversion remain excluded.
The pointer value is captured at the call, so subsequent descriptor assignment
cannot retarget it. Actual byte coverage and lifetime checks remain separate.

Numeric domains do not retain equality provenance. The proof recorder therefore
conservatively attaches eligible getter aliases and frames to all safe checks
in the caller, excluding the current call's own entry checks. This may add
unnecessary conditional dependencies, including at earlier statements; it never
changes an unknown check into a proof. Pointer checks and copied-byte proofs
must retain both assumptions. A bare return postcondition supplies no frame.

Twenty functions cover one direct positive, three conditional getter positives
and sixteen unsafe/unsupported copied reads that must remain unknown. Missing
metadata remains an unmet entry requirement. No unsafe C is executed.

Reproduce from `CodeHawk/`:

```
opam exec -- dune runtest CHT/CHC_tests/cchanalyze_tests/txcchanalyze --force
```

The parser archive retains the LP64 C99 input and scope certificate. This does
not model ES output regions or global TBL descriptors, nor the write getter's
zero-allocation branch. Those require separate contracts and generation models.
