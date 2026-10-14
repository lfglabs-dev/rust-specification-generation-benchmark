import Benchmark.Cases.Goldilocks.Field.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open goldilocks_ntt
open Benchmark.Cases.Goldilocks.Field

namespace Benchmark.Cases.Goldilocks.Field.Oracle

/-- PBT `field::tests::test_construct` (ntt/src/field/mod.rs:261-270):
`prop_assume!(n < algo::MODULUS); let a = Field::new(n); let b = Field::from(n);
 assert_eq!(a, b); assert_eq!(u64::from(a), n);`
`Field::new` computes the Montgomery form with `u128` `*`/`%`, `Field::from(u64)`
with `reduce_64` and `mont_mul(_, MONT_R2)`; `u64::from(Field)` converts back
with `mont_mul(_, 1)`. -/
def construct_roundtrip_spec (n : Std.U64) : Prop :=
  (do
    let a ← field.Field.new n
    let b ← field.Field.Insts.CoreConvertFromU64.from n
    let m ← goldilocks_ntt.U64.Insts.CoreConvertFromField.from a
    ok (a, b, m)) ⦃ r => r.1 = r.2.1 ∧ r.2.2 = n ⦄

/-- PBT `field::tests::test_add_identity` (ntt/src/field/mod.rs:272-278):
`let b = a + Field::new(0); assert_eq!(a, b);` -/
def add_identity_spec (a : field.Field) : Prop :=
  (do
    let zero ← field.Field.new 0#u64
    field.Field.Insts.CoreOpsArithAddFieldField.add a zero) ⦃ b => a = b ⦄

/-- PBT `field::tests::test_add_commutative` (ntt/src/field/mod.rs:280-287):
`let ab = a + b; let ba = b + a; assert_eq!(ab, ba);` -/
def add_commutative_spec (a b : field.Field) : Prop :=
  (do
    let ab ← field.Field.Insts.CoreOpsArithAddFieldField.add a b
    let ba ← field.Field.Insts.CoreOpsArithAddFieldField.add b a
    ok (ab, ba)) ⦃ r => r.1 = r.2 ⦄

/-- PBT `field::tests::test_add_associative` (ntt/src/field/mod.rs:289-296):
`let a_bc = a + (b + c); let ab_c = (a + b) + c; assert_eq!(a_bc, ab_c);` -/
def add_associative_spec (a b c : field.Field) : Prop :=
  (do
    let bc ← field.Field.Insts.CoreOpsArithAddFieldField.add b c
    let a_bc ← field.Field.Insts.CoreOpsArithAddFieldField.add a bc
    let ab ← field.Field.Insts.CoreOpsArithAddFieldField.add a b
    let ab_c ← field.Field.Insts.CoreOpsArithAddFieldField.add ab c
    ok (a_bc, ab_c)) ⦃ r => r.1 = r.2 ⦄

/-- PBT `field::tests::test_sub` (ntt/src/field/mod.rs:298-305):
`let ab = a + b; let ab_b = ab - b; assert_eq!(a, ab_b);` -/
def sub_add_cancel_spec (a b : field.Field) : Prop :=
  (do
    let ab ← field.Field.Insts.CoreOpsArithAddFieldField.add a b
    field.Field.Insts.CoreOpsArithSubFieldField.sub ab b) ⦃ ab_b => a = ab_b ⦄

/-- PBT `field::tests::test_mul_identity` (ntt/src/field/mod.rs:307-313):
`let b = a * Field::new(1); assert_eq!(a, b);` -/
def mul_identity_spec (a : field.Field) : Prop :=
  (do
    let one ← field.Field.new 1#u64
    field.Field.Insts.CoreOpsArithMulFieldField.mul a one) ⦃ b => a = b ⦄

/-- PBT `field::tests::test_mul_commutative` (ntt/src/field/mod.rs:315-322):
`let ab = a * b; let ba = b * a; assert_eq!(ab, ba);` -/
def mul_commutative_spec (a b : field.Field) : Prop :=
  (do
    let ab ← field.Field.Insts.CoreOpsArithMulFieldField.mul a b
    let ba ← field.Field.Insts.CoreOpsArithMulFieldField.mul b a
    ok (ab, ba)) ⦃ r => r.1 = r.2 ⦄

/-- PBT `field::tests::test_mul_associative` (ntt/src/field/mod.rs:324-331):
`let a_bc = a * (b * c); let ab_c = (a * b) * c; assert_eq!(a_bc, ab_c);` -/
def mul_associative_spec (a b c : field.Field) : Prop :=
  (do
    let bc ← field.Field.Insts.CoreOpsArithMulFieldField.mul b c
    let a_bc ← field.Field.Insts.CoreOpsArithMulFieldField.mul a bc
    let ab ← field.Field.Insts.CoreOpsArithMulFieldField.mul a b
    let ab_c ← field.Field.Insts.CoreOpsArithMulFieldField.mul ab c
    ok (a_bc, ab_c)) ⦃ r => r.1 = r.2 ⦄

/-- PBT `field::tests::test_distributive` (ntt/src/field/mod.rs:333-340):
`let a_bc = a * (b + c); let ab_ac = (a * b) + (a * c); assert_eq!(a_bc, ab_ac);` -/
def distributive_spec (a b c : field.Field) : Prop :=
  (do
    let bc ← field.Field.Insts.CoreOpsArithAddFieldField.add b c
    let a_bc ← field.Field.Insts.CoreOpsArithMulFieldField.mul a bc
    let ab ← field.Field.Insts.CoreOpsArithMulFieldField.mul a b
    let ac ← field.Field.Insts.CoreOpsArithMulFieldField.mul a c
    let ab_ac ← field.Field.Insts.CoreOpsArithAddFieldField.add ab ac
    ok (a_bc, ab_ac)) ⦃ r => r.1 = r.2 ⦄

/-! ## Reference equivalences of the `u64` primitives (`ntt/src/field/algo/mod.rs`, module `test`) -/

/-- PBT `field::algo::test::test_add_naive` (ntt/src/field/algo/mod.rs:27-36):
`let value = add(a, b);
 let expected = (u128::from(a) + u128::from(b)).rem_euclid(u128::from(MODULUS)) as u64;
 assert_eq!(value, expected);`
The reference side cannot panic (`a + b < 2^65` fits `u128`, `MODULUS ≠ 0`) and its
remainder is `< MODULUS < 2^64`, so the `as u64` cast is exact: it is the natural
number `(a + b) % MODULUS`. -/
def add_matches_naive_spec (a b : Std.U64) : Prop :=
  field.algo.generic.add a b ⦃ value =>
    value.val = (a.val + b.val) % (2^64 - 2^32 + 1) ⦄

/-- PBT `field::algo::test::test_sub_naive` (ntt/src/field/algo/mod.rs:38-47):
`let value = sub(a, b);
 let expected = (i128::from(a) - i128::from(b)).rem_euclid(i128::from(MODULUS)) as u64;
 assert_eq!(value, expected);`
The reference side cannot panic (`|a - b| < 2^64` fits `i128`, `MODULUS ≠ 0`);
`rem_euclid` by a positive modulus is Lean's `Int.emod` (`%` on `Int`, always in
`[0, MODULUS)`), so the `as u64` cast is exact. -/
def sub_matches_naive_spec (a b : Std.U64) : Prop :=
  field.algo.generic.sub a b ⦃ value =>
    (value.val : Int) = ((a.val : Int) - (b.val : Int)) % (2^64 - 2^32 + 1) ⦄

/-- PBT `field::algo::test::test_mont_pow` (ntt/src/field/algo/mod.rs:153-163):
`let ab = mont_pow(a, b); let ac = mont_pow(a, c); let a_bc = mont_pow(a, b + c);
 let ab_ac = mont_mul(ab, ac); assert_eq!(a_bc, ab_ac);`
`b + c` is Rust's checked `u64` addition, executed in the `do` block. -/
def mont_pow_add_exponents_spec (a b c : Std.U64) : Prop :=
  (do
    let ab ← field.algo.generic.mont_pow a b
    let ac ← field.algo.generic.mont_pow a c
    let bc ← b + c
    let a_bc ← field.algo.generic.mont_pow a bc
    let ab_ac ← field.algo.generic.mont_mul ab ac
    ok (a_bc, ab_ac)) ⦃ r => r.1 = r.2 ⦄

axiom add_matches_naive (a b : Std.U64)
    (h_assume_a : a.val < 2^64 - 2^32 + 1)
    (h_assume_b : b.val < 2^64 - 2^32 + 1) :
    add_matches_naive_spec a b

axiom construct_roundtrip (n : Std.U64)
    (h_assume_n : n.val < 2^64 - 2^32 + 1) :
    construct_roundtrip_spec n

axiom mont_pow_add_exponents (a b c : Std.U64)
    (h_assume_a : a.val < 2^64 - 2^32 + 1)
    (h_b : b.val < 100)
    (h_c : c.val < 100) :
    mont_pow_add_exponents_spec a b c

axiom mul_commutative (a b : field.Field)
    (h_a : a.val < 2^64 - 2^32 + 1)
    (h_b : b.val < 2^64 - 2^32 + 1) :
    mul_commutative_spec a b

axiom sub_matches_naive (a b : Std.U64)
    (h_assume_a : a.val < 2^64 - 2^32 + 1)
    (h_assume_b : b.val < 2^64 - 2^32 + 1) :
    sub_matches_naive_spec a b

end Benchmark.Cases.Goldilocks.Field.Oracle
