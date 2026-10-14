import Benchmark.Cases.Crc32fast.Baseline.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crc32fast
open Benchmark.Cases.Crc32fast.Baseline

namespace Benchmark.Cases.Crc32fast.Baseline.Oracle

/-- PBT `baseline::test::fast_16_is_the_same_as_slow` (src/baseline.rs:79-83), quickcheck:
```rust
fn fast_16_is_the_same_as_slow(crc: u32, bytes: Vec<u8>) -> bool {
    super::update_fast_16(crc, &bytes) == super::update_slow(crc, &bytes)
}
```
Both calls receive `&bytes` (the `Vec<u8>` dereferenced to a `&[u8]`, CoreModels
`Deref for Vec`); the test's `bool` result is `true` iff the two `u32`
checksums are equal. -/
def fast_16_is_the_same_as_slow_spec (crc : Std.U32) (bytes : alloc.vec.Vec Std.U8) : Prop :=
  (do
    let s1 ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref bytes
    let fast ← baseline.update_fast_16 crc s1
    let s2 ← alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref bytes
    let slow ← baseline.update_slow crc s2
    ok (fast, slow)) ⦃ r => r.1 = r.2 ⦄

axiom fast_16_is_the_same_as_slow (crc : Std.U32) (bytes : alloc.vec.Vec Std.U8) :
    fast_16_is_the_same_as_slow_spec crc bytes

end Benchmark.Cases.Crc32fast.Baseline.Oracle
