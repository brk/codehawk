# Object lower bounds require evidence

An opaque external pointer return, a pointer argument and a global pointer value
previously satisfied lower-bound by IH alone. Even an explicit valid-memory
postcondition does not specify a backing object's lower bound. Require a
reverse-buffer return postcondition with a nonnegative extent and retain the
evidence as conditional, including null/explicit reverse-buffer error cases.
Unknown error alternatives prevent this proof. Delegate entry bounds to callers;
do not identify an external field's pointer value with an object's base.

Controls include opaque, valid-only, modeled, nullable/error, malloc, caller and
global-pointer paths. Actual local/global/array objects remain safe. A negative
offset from a real array still violates its separately generated ptr-lower-bound
obligation; parent arithmetic discharges do not erase that obligation. Live
memory, upper bounds, initialization, alignment and ownership remain separate.

Invalid controls are analysis only. The included custom library summaries are
test premises; file contracts do not support their error alternatives. Parser
input contains no prior proofs or inferred invariants.

Run `dune runtest CHT/CHC_tests -j4 --force`.
