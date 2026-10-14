import Benchmark.Cases.Crc32fast.Baseline.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crc32fast

namespace Benchmark.Cases.Crc32fast.Baseline

/-- For every initial CRC value `crc` and every byte vector `bytes`, the
slicing-by-16 implementation `update_fast_16(crc, &bytes)` and the
byte-at-a-time implementation `update_slow(crc, &bytes)` both run without
panicking and return the same CRC-32. -/
def fast_16_is_the_same_as_slow_spec (crc : Std.U32) (bytes : alloc.vec.Vec Std.U8) : Prop :=
  (do
    let s1 ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref bytes
    let fast ← baseline.update_fast_16 crc s1
    let s2 ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref bytes
    let slow ← baseline.update_slow crc s2
    ok (fast, slow)) ⦃ r => r.1 = r.2 ⦄

end Benchmark.Cases.Crc32fast.Baseline
