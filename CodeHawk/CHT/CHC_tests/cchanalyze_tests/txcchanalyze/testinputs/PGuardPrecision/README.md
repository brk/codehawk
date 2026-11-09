LP64 parser-only precision reproducer. Unsafe C never executes.

Before the path-local eligibility repair, guard_error_log_narrow_good stays
unknown: converting status to unsigned in a terminal error log disables the
whole function. The no-log and widening-log controls prove conditionally.

After the repair all three positives retain the exact guarded PostAssumption.
A conversion on a reaching prefix or a rejoining branch still disables the
proof. Normalizing a failed status cannot manufacture output initialization.
Existing 43 guarded-output controls and byte/lifetime controls must still pass.

Only supported structured acyclic flow is eligible. The forward safety pass
matches the translator's CFG contexts and has no Return fallthrough. Joins
require every continuing predecessor safe; unsupported conversions never
restore eligibility. Alias/control-flow exclusions remain global. No new
memory frame, failure preservation, region or payload fact is introduced.
