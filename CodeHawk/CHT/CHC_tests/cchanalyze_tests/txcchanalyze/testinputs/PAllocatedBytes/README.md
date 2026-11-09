Parser-only LP64 allocation controls, never executed.

Eight positive copied reads are conditional on the library malloc new-memory
and byte-buffer postconditions; those dependencies are asserted explicitly.
Thirty-three negative/unsupported controls stay unknown. Initialized source
entry requirements are checked independently of destination reads.

Only a matching nonnull allocation base, positive capacity captured as a
literal call argument, a live call-site token, and a covering memset interval
can prove bytes. Zero-size, nonguarded, failed and foreign allocations grant
no byte proof. Allocation alone never initializes payload. Calls have separate
byte and lifetime invalidation: clearing cannot revive a token killed by free,
realloc, indirect/opaque calls or a failed branch join. Another nonnull pointer
does not validate the requested region. Loop sites and escaped/nested metadata
remain excluded by the existing scope guard.

Typed offsets retain their original stride. A structure-field proof requires
its whole bounded enclosing object cleared, rather than guessing a field byte
offset; over-wide leaf reads are rejected. This intentionally loses partial
field precision. Variable allocation sizes are not reconstructed from later
metadata. Disjoint heap writes/calls can lose facts conservatively. ES pool
output parameters, descriptor getters, global regions and borrow generations
are not inferred from this malloc primitive.

Minimal positive: p=malloc(8); if(!p)return 0; memset(p,0,8);
memcpy(&value,p,4); return value. Without this feature the source stays unknown.
Minimal lifetime negative: free(p); memset(p,0,8); memcpy(&value,p,4).
A byte-interval-only prototype falsely accepted this; the independent lifetime
token is required even after a later full clear. Both controls are retained.
