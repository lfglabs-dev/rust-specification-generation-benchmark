import Benchmark.Cases.NtTime.FileTime.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open nt_time

namespace Benchmark.Cases.NtTime.FileTime

/-- `FileTime::from_be_bytes` never panics and decodes its 8 bytes as a big-endian base-256
number (the value of `FileTime::new(u64::from_be_bytes(bytes))`). -/
def from_be_bytes_roundtrip_spec (bytes : Array Std.U8 8#usize) : Prop :=
  file_time.FileTime.from_be_bytes bytes ⦃ ft =>
    ft.val = (bytes.val.map (·.val)).foldl (fun acc b => 256 * acc + b) 0 ⦄

end Benchmark.Cases.NtTime.FileTime
