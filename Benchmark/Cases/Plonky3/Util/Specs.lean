import Benchmark.Cases.Plonky3.Util.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_util
open Benchmark.Cases.Plonky3.Util

namespace Benchmark.Cases.Plonky3.Util.Oracle

/-- PBT `tests::test_log3_strict_roundtrip` (util/src/lib.rs:1304-1309):

```rust
fn test_log3_strict_roundtrip(k in 0u32..25u32) {
    let n = 3usize.pow(k);
    assert_eq!(log3_strict_usize(n), k as usize);
}
```

`3usize.pow(k)` is evaluated with the CoreModels model of `usize::pow`
(`core.num.Usize.pow`, which fails on overflow as in a debug build), and
`k as usize` is the lossless widening, i.e. the value `k.val`. -/
def log3_strict_roundtrip_spec (k : Std.U32) : Prop :=
  (do
    let n ← core.num.Usize.pow 3#usize k
    log3_strict_usize n) ⦃ r => r.val = k.val ⦄

axiom log3_strict_roundtrip (k : Std.U32)
    (h_k : k.val < 25)
    (h_platform : System.Platform.numBits = 64) :
    log3_strict_roundtrip_spec k

end Benchmark.Cases.Plonky3.Util.Oracle
