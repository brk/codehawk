# Null casts and absolute-address proof order

The old statement checker discharged `not-null((const char *)(void *)0)` as
an absolute memory address. Its general constant-address cases preceded the
null-pointer case. Five direct/two-cast/macro/dereference checks falsely proved;
the three-cast control already reported a violation because it reached the
later null rule. No unsafe C is executed.

Check recognized null pointer constants before general address cases. Six
negative controls must report violations; four actual local/global/literal
address controls retain their proofs. This changes no other absolute-address,
pointer-arithmetic, validity or platform-mapping policy.

Reproduce from `CodeHawk/`:

```
opam exec -- dune runtest CHT/CHC_tests/cchanalyze_tests/txcchanalyze --force
```

The cFS witness was an inferred `not-null(DefaultString)` call obligation for
`CFE_SB_MessageStringGet(..., NULL, ...)` in DS. That real helper permits a null
default string. Correctly reporting the literal nonnull predicate as false does
not establish an application defect: the callee's inferred precondition still
needs source review and a nullable interface model.
