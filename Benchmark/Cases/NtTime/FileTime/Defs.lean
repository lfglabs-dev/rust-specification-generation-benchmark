import NtTimeFileTime.Extraction

/-!
# nt-time (`FileTime`) — specifications

Implementation: `extracted/NtTimeFileTime` (verbatim `cargo hax extract
nt-time-file-time` output for sorairolake/nt-time@a91cf3fb).

`FileTime` is `#[repr(transparent)] struct FileTime(u64)`; the extraction flattens the
newtype, so `file_time.FileTime` is (reducibly) `Std.U64` and `ft.val` is the raw tick
count (`ft.to_raw()`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in the
extracted code follows Rust debug-build semantics (overflow panics), which is the
configuration `cargo test` runs the original property tests under.

Reference sides of the form `u64::to_be_bytes(raw)`, `(raw >> 32) as u32`,
`(u64::from(high) << 32) | u64::from(low)` or `u64::from_le_bytes(bytes)` cannot panic;
they are stated by their exact mathematical value (base-256 digits, `/ 2^32`,
`% 2^32`, `high * 2^32 + low`, base-256 Horner folds), as allowed by the authoring
playbook. Stated literally they would be the very same library calls the
implementation makes, and the property would hold by unfolding alone.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.NtTime.FileTime

open nt_time

/-! ## Byte-order conversions (`src/file_time.rs`) -/

end Benchmark.Cases.NtTime.FileTime
