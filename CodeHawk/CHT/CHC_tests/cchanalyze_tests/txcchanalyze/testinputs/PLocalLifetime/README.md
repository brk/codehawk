Parser-only LP64 controls; unsafe C is never executed.

CIL flattens the inner block of ended_block_bad into one instruction list.
Before this repair, both ended_block_bad and ended_branch_bad were incorrectly
proved initialized by the local alias feature. Merely rejecting Block/If in the
lowered AST cannot repair the straight-line block case.

The parser enables Cabs2cil.addNestedScopeAttr and certifies that metadata in
the function body. Alias slots and backing objects with goblint_cil_nested are
unsupported, even for valid uses within their scope. Legacy parser files lack
the certificate and cannot enable alias lookup. This does not reconstruct an
exact block lifetime or assume that a pointer stays valid after scope exit.

Three positive controls prove: a function-scope alias, a function-scope alias
cleared on both branches, and a direct nested read within its scope. Seven
negative/unsupported controls stay open: ended block, branch, compound literal,
GNU statement expression, shadowed local, live nested backing, and nested slot.
The latter two are intentional conservative losses. Alias/LocalBytes archives
are reparsed with the same scope-aware parser to retain their existing controls.

Integration evidence in cFS additionally replays an unmodified legacy parser
archive with the repaired engine: all four reads remain unknown, including the
function-scope positive for which that old input lacks lifetime metadata.
