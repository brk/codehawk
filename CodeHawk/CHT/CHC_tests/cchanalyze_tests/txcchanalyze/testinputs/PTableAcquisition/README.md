Parser-only native LP64 controls; unsafe C is analyzed, never executed.

GetAddress has an initialized output pointer value postcondition and requires a
nonnull writable eight-byte slot. It has no complete write footprint and grants
no table contents, extent, successful validation, alignment or lifetime.

Four pointer-value reads retain contract dependencies, including failure and
field/cast slots. An undersized slot remains violated. Explicit byte-size five
requires five bytes, while index-size two still requires two uint32 elements.
Pointee reads/copies, sibling values and released/opaque-call frames stay open.
