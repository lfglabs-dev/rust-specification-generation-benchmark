import Benchmark.Cases.RevBits.U32.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open rev_bits
open Benchmark.Cases.RevBits.U32

namespace Benchmark.Cases.RevBits.U32.Oracle

/-- PBT `u32::range::tests::identity_is_correct` (src/u32/range.rs:133-136):
`identity(x) == std::cmp::min(x, BITS - 1)`. -/
def identity_is_correct_spec (x : Std.U32) : Prop :=
  u32.range.identity x ⦃ r => r.val = min x.val 31 ⦄

/-- PBT `u32::range::tests::increment_is_correct` (src/u32/range.rs:116-124):
```
let inc = increment(x);
if x == std::u32::MAX { inc == BITS - 1 } else { inc == std::cmp::min(x + 1, BITS - 1) }
```
In the `else` branch `x < u32::MAX`, so the test's own `x + 1` cannot
overflow and equals the natural-number sum `x.val + 1`. -/
def increment_is_correct_spec (x : Std.U32) : Prop :=
  u32.range.increment x ⦃ inc =>
    if x.val = 2^32 - 1 then inc.val = 31          -- x == u32::MAX
    else inc.val = min (x.val + 1) 31 ⦄

/-- PBT `u32::range::tests::decrement_is_correct` (src/u32/range.rs:99-107):
```
let dec = decrement(x);
if x == 0 { dec == 0 } else { dec == std::cmp::min(x - 1, BITS - 1) }
```
In the `else` branch `x ≥ 1`, so the test's own `x - 1` cannot underflow and
equals the natural-number difference `x.val - 1`. -/
def decrement_is_correct_spec (x : Std.U32) : Prop :=
  u32.range.decrement x ⦃ dec =>
    if x.val = 0 then dec.val = 0
    else dec.val = min (x.val - 1) 31 ⦄

/-- PBT `u32::ref_impl::tests::to_array_to_u32` (src/u32/ref_impl.rs:90-93):
`x == to_u32(&to_array(x))`. The borrow `&to_array(x)` coerces the
`[bool; 32]` array to a `&[bool]` slice, which the extraction models with
`Array.to_slice` (exactly as Aeneas emits it for such coercions). -/
def to_array_to_u32_spec (x : Std.U32) : Prop :=
  (do
    let array ← u32.ref_impl.to_array x
    let slice ← lift (Array.to_slice array)
    u32.ref_impl.to_u32 slice) ⦃ r => r = x ⦄

axiom decrement_is_correct (x : Std.U32) :
    decrement_is_correct_spec x

axiom to_array_to_u32 (x : Std.U32) :
    to_array_to_u32_spec x

end Benchmark.Cases.RevBits.U32.Oracle
