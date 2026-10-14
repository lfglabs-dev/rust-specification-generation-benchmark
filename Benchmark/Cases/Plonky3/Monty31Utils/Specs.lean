import Benchmark.Cases.Plonky3.Monty31Utils.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open p3_monty_31
open Benchmark.Cases.Plonky3.Monty31Utils

namespace Benchmark.Cases.Plonky3.Monty31Utils.Oracle

/-- PBT `utils::tests::kb_to_from_monty_roundtrip` (monty-31/src/utils.rs:267):
`prop_assert_eq!(from_monty::<KB>(to_monty::<KB>(x)), x)`. -/
def kb_to_from_monty_roundtrip_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U32) : Prop :=
  (do
    let m ← utils.to_monty inst x
    utils.from_monty inst m) ⦃ r => r.val = x.val ⦄

/-- PBT `utils::tests::bb_from_to_monty_roundtrip` (monty-31/src/utils.rs:285):
`prop_assert_eq!(to_monty::<BB>(from_monty::<BB>(m)), m)`. -/
def bb_from_to_monty_roundtrip_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (m : Std.U32) : Prop :=
  (do
    let x ← utils.from_monty inst m
    utils.to_monty inst x) ⦃ r => r.val = m.val ⦄

/-- PBT `utils::tests::kb_to_monty_output_range` (monty-31/src/utils.rs:294):
`prop_assert!(to_monty::<KB>(x) < KB_P)`. -/
def kb_to_monty_output_range_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U32) : Prop :=
  utils.to_monty inst x ⦃ r => r.val < 2130706433 ⦄

/-- PBT `utils::tests::bb_to_monty_64_extends_32` (monty-31/src/utils.rs:364):
`prop_assert_eq!(to_monty_64::<BB>(x as u64), to_monty::<BB>(x))`. -/
def bb_to_monty_64_extends_32_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U32) : Prop :=
  (do
    let wide ← utils.to_monty_64 inst (UScalar.cast .U64 x)
    let narrow ← utils.to_monty inst x
    ok (wide, narrow)) ⦃ p => p.1.val = p.2.val ⦄

/-! ## Modular addition / subtraction -/

/-- PBT `utils::tests::kb_add_commutative` (monty-31/src/utils.rs:392):
`prop_assert_eq!(add::<KB>(a, b), add::<KB>(b, a))`. -/
def kb_add_commutative_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (a b : Std.U32) : Prop :=
  (do
    let ab ← utils.add inst a b
    let ba ← utils.add inst b a
    ok (ab, ba)) ⦃ p => p.1.val = p.2.val ⦄

/-- PBT `utils::tests::bb_add_sub_roundtrip` (monty-31/src/utils.rs:413):
`prop_assert_eq!(sub::<BB>(add::<BB>(a, b), b), a)`. -/
def bb_add_sub_roundtrip_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (a b : Std.U32) : Prop :=
  (do
    let s ← utils.add inst a b
    utils.sub inst s b) ⦃ r => r.val = a.val ⦄

/-- PBT `utils::tests::kb_sub_add_roundtrip` (monty-31/src/utils.rs:418):
`prop_assert_eq!(add::<KB>(sub::<KB>(a, b), b), a)`. -/
def kb_sub_add_roundtrip_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (a b : Std.U32) : Prop :=
  (do
    let d ← utils.sub inst a b
    utils.add inst d b) ⦃ r => r.val = a.val ⦄

/-! ## Montgomery reduction -/

/-- PBT `utils::tests::bb_monty_reduce_output_range` (monty-31/src/utils.rs:442):
`prop_assert!(monty_reduce::<BB>(x) < BB_P)`. -/
def bb_monty_reduce_output_range_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U64) : Prop :=
  utils.monty_reduce inst x ⦃ r => r.val < 2013265921 ⦄

/-- PBT `utils::tests::kb_monty_reduce_identity` (monty-31/src/utils.rs:447):
`let result = monty_reduce::<KB>(x) as u64;
prop_assert_eq!((result * R) % KB_P as u64, x % KB_P as u64)` with `R = 1u64 << 32`.
(`result * R` cannot overflow `u64`: `result < 2^32`, so it is stated in `Nat`.) -/
def kb_monty_reduce_identity_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U64) : Prop :=
  utils.monty_reduce inst x ⦃ r => r.val * 2^32 % 2130706433 = x.val % 2130706433 ⦄

/-- PBT `utils::tests::kb_large_agrees_with_standard` (monty-31/src/utils.rs:465):
`prop_assert_eq!(large_monty_reduce::<KB>(x), monty_reduce::<KB>(x))`. -/
def kb_large_agrees_with_standard_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U64) : Prop :=
  (do
    let large ← utils.large_monty_reduce inst x
    let standard ← utils.monty_reduce inst x
    ok (large, standard)) ⦃ p => p.1.val = p.2.val ⦄

/-- PBT `utils::tests::kb_large_monty_reduce_output_range` (monty-31/src/utils.rs:475):
`prop_assert!(large_monty_reduce::<KB>(x) < KB_P)`. -/
def kb_large_monty_reduce_output_range_spec {MP : Type}
    (inst : data_traits.MontyParameters MP) (x : Std.U64) : Prop :=
  utils.large_monty_reduce inst x ⦃ r => r.val < 2130706433 ⦄

/-- PBT `utils::tests::bb_large_monty_reduce_identity` (monty-31/src/utils.rs:491):
`let result = large_monty_reduce::<BB>(x) as u64;
prop_assert_eq!((result * R) % BB_P as u64, x % BB_P as u64)` with `R = 1u64 << 32`.
(`result * R` cannot overflow `u64`: `result < 2^32`, so it is stated in `Nat`.) -/
def bb_large_monty_reduce_identity_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (x : Std.U64) : Prop :=
  utils.large_monty_reduce inst x ⦃ r => r.val * 2^32 % 2013265921 = x.val % 2013265921 ⦄

/-! ## 128-bit Montgomery reduction -/

/-- PBT `utils::tests::kb_monty_reduce_u128_output_range` (monty-31/src/utils.rs:502):
`let x = (hi as u128) << 64 | lo as u128; prop_assert!(monty_reduce_u128::<KB>(x) < KB_P)`.
The test's construction of `x` is executed with the Rust primitives (`as u128`, `<< 64`
with an `i32` shift amount, `|`). -/
def kb_monty_reduce_u128_output_range_spec {MP : Type}
    (inst : data_traits.MontyParameters MP) (lo : Std.U64) (hi : Std.U32) : Prop :=
  (do
    let hi_shifted ← UScalar.cast .U128 hi <<< 64#i32
    let x := hi_shifted ||| UScalar.cast .U128 lo
    utils.monty_reduce_u128 inst x) ⦃ r => r.val < 2130706433 ⦄

/-- PBT `utils::tests::kb_monty_reduce_u128_identity` (monty-31/src/utils.rs:514):
`let x = (hi as u128) << 64 | lo as u128; let result = monty_reduce_u128::<KB>(x) as u128;
prop_assert_eq!((result * R as u128) % KB_P as u128, x % KB_P as u128)`.
(`result * R` cannot overflow `u128`: `result < 2^32`, so it is stated in `Nat`.) -/
def kb_monty_reduce_u128_identity_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (lo : Std.U64) (hi : Std.U32) : Prop :=
  (do
    let hi_shifted ← UScalar.cast .U128 hi <<< 64#i32
    let x := hi_shifted ||| UScalar.cast .U128 lo
    let result ← utils.monty_reduce_u128 inst x
    ok (x, result)) ⦃ p => p.2.val * 2^32 % 2130706433 = p.1.val % 2130706433 ⦄

/-- PBT `utils::tests::bb_monty_reduce_u128_agrees_with_u64` (monty-31/src/utils.rs:536):
`prop_assert_eq!(monty_reduce_u128::<BB>(x as u128), monty_reduce::<BB>(x))`. -/
def bb_monty_reduce_u128_agrees_with_u64_spec {MP : Type}
    (inst : data_traits.MontyParameters MP) (x : Std.U64) : Prop :=
  (do
    let wide ← utils.monty_reduce_u128 inst (UScalar.cast .U128 x)
    let narrow ← utils.monty_reduce inst x
    ok (wide, narrow)) ⦃ p => p.1.val = p.2.val ⦄

/-! ## Montgomery multiplication -/

/-- PBT `utils::tests::kb_monty_mul_correct` (monty-31/src/utils.rs:555):
```rust
let product = to_monty::<KB>(a) as u64 * to_monty::<KB>(b) as u64;
let expected = to_monty::<KB>(((a as u64 * b as u64) % KB_P as u64) as u32);
prop_assert_eq!(monty_reduce::<KB>(product), expected);
```
The test's own arithmetic (`*` and `%` on `u64`, `as` casts) is executed with the
Rust primitives, in the test's evaluation order. -/
def kb_monty_mul_correct_spec {MP : Type} (inst : data_traits.MontyParameters MP)
    (a b : Std.U32) : Prop :=
  (do
    let ma ← utils.to_monty inst a
    let mb ← utils.to_monty inst b
    let product ← UScalar.cast .U64 ma * UScalar.cast .U64 mb
    let ab ← UScalar.cast .U64 a * UScalar.cast .U64 b
    let ab_mod ← ab % 2130706433#u64
    let expected ← utils.to_monty inst (UScalar.cast .U32 ab_mod)
    let reduced ← utils.monty_reduce inst product
    ok (reduced, expected)) ⦃ p => p.1.val = p.2.val ⦄

axiom bb_add_sub_roundtrip {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (a b : Std.U32)
    (h_a : a.val < 2013265921) (h_b : b.val < 2013265921) :
    bb_add_sub_roundtrip_spec inst a b

axiom bb_from_to_monty_roundtrip {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (m : Std.U32)
    (h_m : m.val < 2013265921) :
    bb_from_to_monty_roundtrip_spec inst m

axiom bb_large_monty_reduce_identity {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (x : Std.U64)
    (h_x : x.val < 2013265921 * 2^32 * 2) :
    bb_large_monty_reduce_identity_spec inst x

axiom bb_monty_reduce_output_range {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (x : Std.U64)
    (h_x : x.val < 2013265921 * 2^32) :
    bb_monty_reduce_output_range_spec inst x

axiom bb_monty_reduce_u128_agrees_with_u64 {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (x : Std.U64)
    (h_x : x.val < 2013265921 * 2^32) :
    bb_monty_reduce_u128_agrees_with_u64_spec inst x

axiom bb_to_monty_64_extends_32 {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : BBParams inst) (x : Std.U32) :
    bb_to_monty_64_extends_32_spec inst x

axiom kb_add_commutative {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (a b : Std.U32)
    (h_a : a.val < 2130706433) (h_b : b.val < 2130706433) :
    kb_add_commutative_spec inst a b

axiom kb_large_agrees_with_standard {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (x : Std.U64)
    (h_x : x.val < 2130706433 * 2^32) :
    kb_large_agrees_with_standard_spec inst x

axiom kb_large_monty_reduce_output_range {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (x : Std.U64)
    (h_x : x.val < 2130706433 * 2^32 * 2) :
    kb_large_monty_reduce_output_range_spec inst x

axiom kb_monty_mul_correct {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (a b : Std.U32)
    (h_a : a.val < 2130706433) (h_b : b.val < 2130706433) :
    kb_monty_mul_correct_spec inst a b

axiom kb_monty_reduce_identity {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (x : Std.U64)
    (h_x : x.val < 2130706433 * 2^32) :
    kb_monty_reduce_identity_spec inst x

axiom kb_monty_reduce_u128_identity {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (lo : Std.U64) (hi : Std.U32) :
    kb_monty_reduce_u128_identity_spec inst lo hi

axiom kb_to_from_monty_roundtrip {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (x : Std.U32)
    (h_x : x.val < 2130706433) :
    kb_to_from_monty_roundtrip_spec inst x

axiom kb_to_monty_output_range {MP : Type} (inst : data_traits.MontyParameters MP)
    (h_params : KBParams inst) (x : Std.U32) :
    kb_to_monty_output_range_spec inst x

end Benchmark.Cases.Plonky3.Monty31Utils.Oracle
