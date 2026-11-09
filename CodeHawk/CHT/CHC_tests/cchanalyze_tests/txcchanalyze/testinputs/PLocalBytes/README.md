Parser-only LP64 local memset byte-range controls; unsafe C is never run.

One exact interval per local object, relative to a known subobject. Full clears
cover valid constant-index nested subobjects without guessing structure layout.
Partial clears cover only the recorded byte interval. Branch joins require all
alternative intervals to cover the request. Any write into the same object
forgets its interval; unknown/indirect/unframed calls forget all intervals.
Reviewed read-only/disjoint-write contracts preserve them conditionally with
explicit PostAssumption dependencies. Only lib:string memset supplies a fact;
generic initialized-range/post-only effects do not.

The scope is acyclic lowered functions, fixed local extents and syntactic local
addresses. Loops/gotos/switch/VLAs/assembly remain unsupported for seeding because
CIL's flattened declarations do not establish block lifetimes across cycles.
No production analysis is skipped and no loop bound/capacity is changed. Pointer
aliases, descriptor-held pointers, allocator results and callback parameters
remain unknown. Separate partial clears are not merged. The actual WDT copy
reads remain open; this feature first proves the local cleared aggregate.
