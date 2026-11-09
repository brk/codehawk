Parser-only LP64 controls. Unsafe functions never execute.

initialized-on-return(op,constant,lval) means return op constant implies
initialized(lval); it grants nothing on other returns and no memory frame.
All 16 positives must retain this full guarded PostAssumption. The 27 negative
or unsupported reads remain open. Six comparison forms round-trip through
MathML and the interface dictionary without losing the signed constant.

The guard needs a matching immutable call result plus a proving interval at
the read. Another call, overwritten/normalized/masked/arithmetic status,
unchecked failure, narrowing/bool casts, partial/union/volatile status storage,
branch gaps and release cannot establish it. Saved and widened full-value
statuses, ordinary fields and explicitly framed calls are checked positively.
The framed two-call negative ensures correct call identity is needed even
when the later call preserves the earlier output object.

Cycles, unsupported conversions, addressed/global/union status assignments,
explicit fixed global values and old uncertified parser inputs are excluded
conservatively. The pointer slot becomes initialized, not its payload, backing
extent, validity or lifetime. A narrow union-field promise cannot initialize
the wider field. Opaque calls retain havoc; failure preservation is not assumed.

Only integral callee results can establish a return guard. Floating-point
guards stay unsupported; in particular, !(r<0) would not imply r>=0 for NaN.
No finite-result assumption is introduced. The float control stays unknown.
