The parser input mirrors LC_CopyBytesWithSwap. Its conditional model requires
NumBytes <= 4, four initialized source bytes, initialized map bytes for the
requested count, and an initialized full destination word on entry. This is a
deliberately stronger contract than the minimal source span of valid 16-bit
conversion maps. It asserts no successful table/buffer acquisition.

The native test checks that initialized field reads retain their contract
dependency and that constant extent casts preserve their values. Frontend
integration checks the map-byte proofs and the supporting obligations:
positive full/partial calls have discharged entry requirements; truncated,
uninitialized/partial-source, uninitialized-map, uninitialized-tail and
oversized controls retain unknown or violated requirements. Conditional
postconditions alone do not prove those callers safe. Unsafe C is analyzed,
never executed.
