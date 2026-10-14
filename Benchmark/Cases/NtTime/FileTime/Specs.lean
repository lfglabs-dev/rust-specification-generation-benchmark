import Benchmark.Cases.NtTime.FileTime.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time
open Benchmark.Cases.NtTime.FileTime

namespace Benchmark.Cases.NtTime.FileTime.Oracle

/-- PBT `file_time::tests::to_be_bytes_roundtrip` (src/file_time.rs:482-487):
`prop_assert_eq!(ft.to_be_bytes(), ft.to_raw().to_be_bytes())`.
The right-hand side is the big-endian byte sequence of the raw value: byte `i` is
`raw / 256^(7-i) % 256`. -/
def to_be_bytes_roundtrip_spec (ft : file_time.FileTime) : Prop :=
  (do
    let bytes ← file_time.FileTime.to_be_bytes ft
    let raw ← file_time.FileTime.to_raw ft
    ok (bytes, raw)) ⦃ r =>
      r.1.val.map (·.val) =
        [r.2.val / 2^56 % 2^8, r.2.val / 2^48 % 2^8, r.2.val / 2^40 % 2^8,
         r.2.val / 2^32 % 2^8, r.2.val / 2^24 % 2^8, r.2.val / 2^16 % 2^8,
         r.2.val / 2^8 % 2^8, r.2.val % 2^8] ⦄

/-- PBT `file_time::tests::to_le_bytes_roundtrip` (src/file_time.rs:507-512):
`prop_assert_eq!(ft.to_le_bytes(), ft.to_raw().to_le_bytes())`.
The right-hand side is the little-endian byte sequence of the raw value: byte `i` is
`raw / 256^i % 256`. -/
def to_le_bytes_roundtrip_spec (ft : file_time.FileTime) : Prop :=
  (do
    let bytes ← file_time.FileTime.to_le_bytes ft
    let raw ← file_time.FileTime.to_raw ft
    ok (bytes, raw)) ⦃ r =>
      r.1.val.map (·.val) =
        [r.2.val % 2^8, r.2.val / 2^8 % 2^8, r.2.val / 2^16 % 2^8,
         r.2.val / 2^24 % 2^8, r.2.val / 2^32 % 2^8, r.2.val / 2^40 % 2^8,
         r.2.val / 2^48 % 2^8, r.2.val / 2^56 % 2^8] ⦄

/-- PBT `file_time::tests::from_be_bytes_roundtrip` (src/file_time.rs:568-576):
`prop_assert_eq!(FileTime::from_be_bytes(bytes), FileTime::new(u64::from_be_bytes(bytes)))`.
`u64::from_be_bytes(bytes)` is the base-256 number whose most significant digit is
`bytes[0]` (Horner evaluation `((b0 * 256 + b1) * 256 + ...) * 256 + b7`, written as a
left fold); `FileTime::new` wraps it unchanged. -/
def from_be_bytes_roundtrip_spec (bytes : Array Std.U8 8#usize) : Prop :=
  file_time.FileTime.from_be_bytes bytes ⦃ ft =>
    ft.val = (bytes.val.map (·.val)).foldl (fun acc b => 256 * acc + b) 0 ⦄

/-- PBT `file_time::tests::from_le_bytes_roundtrip` (src/file_time.rs:599-607):
`prop_assert_eq!(FileTime::from_le_bytes(bytes), FileTime::new(u64::from_le_bytes(bytes)))`.
`u64::from_le_bytes(bytes)` is the base-256 number whose least significant digit is
`bytes[0]` (`b0 + 256 * (b1 + 256 * (... + 256 * b7))`, written as a right fold);
`FileTime::new` wraps it unchanged. -/
def from_le_bytes_roundtrip_spec (bytes : Array Std.U8 8#usize) : Prop :=
  file_time.FileTime.from_le_bytes bytes ⦃ ft =>
    ft.val = (bytes.val.map (·.val)).foldr (fun b acc => b + 256 * acc) 0 ⦄

/-! ## High/low `u32` halves (`src/file_time.rs`) -/

/-- PBT `file_time::tests::to_high_low_roundtrip` (src/file_time.rs:666-672):
`let raw = ft.to_raw();
 prop_assert_eq!(ft.to_high_low(), ((raw >> u32::BITS) as u32, raw as u32))`.
`(raw >> 32) as u32` is `raw / 2^32` (< 2^32, no truncation) and `raw as u32` is
`raw % 2^32`. -/
def to_high_low_roundtrip_spec (ft : file_time.FileTime) : Prop :=
  (do
    let raw ← file_time.FileTime.to_raw ft
    let hl ← file_time.FileTime.to_high_low ft
    ok (raw, hl)) ⦃ r =>
      r.2.1.val = r.1.val / 2^32 ∧ r.2.2.val = r.1.val % 2^32 ⦄

/-- PBT `file_time::tests::from_high_low_roundtrip` (src/file_time.rs:695-701):
`let raw = (u64::from(high) << u32::BITS) | u64::from(low);
 prop_assert_eq!(FileTime::from_high_low(high, low), FileTime::new(raw))`.
Since `low < 2^32` and `high < 2^32`, `raw = high * 2^32 + low` (no bits are shifted
out and the `|` is a disjoint sum). -/
def from_high_low_roundtrip_spec (high low : Std.U32) : Prop :=
  file_time.FileTime.from_high_low high low ⦃ ft =>
    ft.val = high.val * 2^32 + low.val ⦄

/-! ## Unix time conversions (`src/file_time/unix_time.rs`) -/

/-- PBT `file_time::unix_time::tests::to_unix_time_nanos_roundtrip`
(src/file_time/unix_time.rs:688-693):
`let ts = ft.to_unix_time_nanos();
 prop_assert!((-11_644_473_600_000_000_000..=1_833_029_933_770_955_161_500).contains(&ts))`. -/
def to_unix_time_nanos_roundtrip_spec (ft : file_time.FileTime) : Prop :=
  file_time.unix_time.FileTime.to_unix_time_nanos ft ⦃ ts =>
    -11644473600000000000 ≤ ts.val ∧ ts.val ≤ 1833029933770955161500 ⦄

/-- PBT `file_time::unix_time::tests::from_unix_time_secs_before_nt_time_epoch_roundtrip`
(src/file_time/unix_time.rs:916-925):
`prop_assert_eq!(FileTime::from_unix_time_secs(ts).unwrap_err(),
 FileTimeRangeErrorKind::Negative.into())`.
`unwrap_err` panics on `Ok`, so the result must be `Err e` with `e` equal (derived
structural `PartialEq`) to `FileTimeRangeErrorKind::Negative.into()`, which is computed
with the extracted `From<FileTimeRangeErrorKind> for FileTimeRangeError` impl. -/
def from_unix_time_secs_before_nt_time_epoch_roundtrip_spec (ts : Std.I64) : Prop :=
  (do
    let r ← file_time.unix_time.FileTime.from_unix_time_secs ts
    let expected ← core.convert.Into.Blanket.into
      error.FileTimeRangeError.Insts.CoreConvertFromFileTimeRangeErrorKind
      error.FileTimeRangeErrorKind.Negative
    ok (r, expected)) ⦃ p => p.1 = core.result.Result.Err p.2 ⦄

/-- PBT `file_time::unix_time::tests::from_unix_time_secs_roundtrip`
(src/file_time/unix_time.rs:959-963):
`prop_assert!(FileTime::from_unix_time_secs(ts).is_ok())`. -/
def from_unix_time_secs_roundtrip_spec (ts : Std.I64) : Prop :=
  (do
    let r ← file_time.unix_time.FileTime.from_unix_time_secs ts
    core.result.Result.is_ok r) ⦃ b => b = true ⦄

/-- PBT `file_time::unix_time::tests::from_unix_time_secs_with_too_big_date_time_roundtrip`
(src/file_time/unix_time.rs:977-986):
`prop_assert_eq!(FileTime::from_unix_time_secs(ts).unwrap_err(),
 FileTimeRangeErrorKind::Overflow.into())`. -/
def from_unix_time_secs_with_too_big_date_time_roundtrip_spec (ts : Std.I64) : Prop :=
  (do
    let r ← file_time.unix_time.FileTime.from_unix_time_secs ts
    let expected ← core.convert.Into.Blanket.into
      error.FileTimeRangeError.Insts.CoreConvertFromFileTimeRangeErrorKind
      error.FileTimeRangeErrorKind.Overflow
    ok (r, expected)) ⦃ p => p.1 = core.result.Result.Err p.2 ⦄

axiom from_be_bytes_roundtrip (bytes : Std.Array Std.U8 8#usize) :
    from_be_bytes_roundtrip_spec bytes

axiom from_high_low_roundtrip (high low : Std.U32) :
    from_high_low_roundtrip_spec high low

axiom from_unix_time_secs_before_nt_time_epoch_roundtrip (ts : Std.I64)
    (h_ts : ts.val ≤ -11644473601) :
    from_unix_time_secs_before_nt_time_epoch_roundtrip_spec ts

axiom from_unix_time_secs_roundtrip (ts : Std.I64)
    (h_ts_lo : -11644473600 ≤ ts.val)
    (h_ts_hi : ts.val ≤ 1833029933770) :
    from_unix_time_secs_roundtrip_spec ts

axiom from_unix_time_secs_with_too_big_date_time_roundtrip (ts : Std.I64)
    (h_ts : 1833029933771 ≤ ts.val) :
    from_unix_time_secs_with_too_big_date_time_roundtrip_spec ts

axiom to_be_bytes_roundtrip (ft : file_time.FileTime) :
    to_be_bytes_roundtrip_spec ft

axiom to_high_low_roundtrip (ft : file_time.FileTime) :
    to_high_low_roundtrip_spec ft

axiom to_le_bytes_roundtrip (ft : file_time.FileTime) :
    to_le_bytes_roundtrip_spec ft

axiom to_unix_time_nanos_roundtrip (ft : file_time.FileTime) :
    to_unix_time_nanos_roundtrip_spec ft

end Benchmark.Cases.NtTime.FileTime.Oracle
