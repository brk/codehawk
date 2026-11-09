Parser-only LP64 initialized-entry controls; unsafe C is not executed.

Both functions may preserve an output on some return paths. Their initialized
postconditions therefore require initialized scalar/field entry slots. Good
callers discharge entry requirements; uninitialized and sibling-only callers
keep unknown entry requirements while output reads remain conditional.
