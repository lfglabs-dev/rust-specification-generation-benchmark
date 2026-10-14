import Benchmark.Cases.CryptoBigint.Uint.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crypto_bigint
open Benchmark.Cases.CryptoBigint.Uint

namespace Benchmark.Cases.CryptoBigint.Uint.Oracle

/-- PBT `roundtrip` (tests/uint.rs:88-91):
```
fn roundtrip(a in uint()) {
    prop_assert_eq!(a, to_uint(to_biguint(&a)));
}
```
`to_biguint(&a)` has value `uintVal a`; `to_uint` builds the 32-byte
little-endian buffer `leBytes32 (uintVal a)` and decodes it with the crate's
`U256::from_le_slice(&input)` (the `&[u8; 32]` → `&[u8]` coercion is
`Array.to_slice`). The assertion compares the decoded `U256` with `a`. -/
def le_bytes_roundtrip_spec (a : uint.Uint 4#usize) : Prop :=
  (uint.encoding.Uint.from_le_slice 4#usize (Array.to_slice (leBytes32 (uintVal a))))
    ⦃ r => r = a ⦄

/-- PBT `wrapping_add` (tests/uint.rs:143-152):
```
fn wrapping_add(a in uint(), b in uint()) {
    let expected = to_uint(a_bi + b_bi);
    let actual = a.wrapping_add(&b);
    prop_assert_eq!(expected, actual);
}
```
`expected` has value `(uintVal a + uintVal b) % 2^256`. -/
def wrapping_add_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  (uint.add.Uint.wrapping_add a b) ⦃ r => uintVal r = (uintVal a + uintVal b) % 2^256 ⦄

/-- PBT `wrapping_sub` (tests/uint.rs:214-227):
```
fn wrapping_sub(mut a in uint(), mut b in uint()) {
    if b > a { mem::swap(&mut a, &mut b); }
    let expected = to_uint(a_bi - b_bi);
    let actual = a.wrapping_sub(&b);
    prop_assert_eq!(expected, actual);
}
```
After the swap `a` holds the larger and `b` the smaller input (`hi`/`lo`
below), so the `BigUint` subtraction `a_bi - b_bi` does not underflow and
`expected` has value `(uintVal hi - uintVal lo) % 2^256`. -/
def wrapping_sub_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  let hi := if uintVal b > uintVal a then b else a -- `a` after the swap
  let lo := if uintVal b > uintVal a then a else b -- `b` after the swap
  (uint.sub.Uint.wrapping_sub hi lo) ⦃ r => uintVal r = (uintVal hi - uintVal lo) % 2^256 ⦄

/-- PBT `sub_mod_nist_p256` (tests/uint.rs:172-192):
```
fn sub_mod_nist_p256(mut a in uint_mod_p(P), mut b in uint_mod_p(P)) {
    if b > a { mem::swap(&mut a, &mut b); }
    prop_assert!(a < P);
    prop_assert!(b < P);
    let expected = to_uint((a_bi - b_bi) % p_bi);
    let actual = a.sub_mod(&b, P.as_nz_ref());
    prop_assert!(expected < P);
    prop_assert!(actual < P);
    prop_assert_eq!(expected, actual);
}
```
`hi`/`lo` are `a`/`b` after the swap; `expected` has value
`((uintVal hi - uintVal lo) % uintVal P) % 2^256`. All five assertions are
kept, in order. -/
def sub_mod_nist_p256_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  let hi := if uintVal b > uintVal a then b else a -- `a` after the swap
  let lo := if uintVal b > uintVal a then a else b -- `b` after the swap
  let expected := ((uintVal hi - uintVal lo) % uintVal P) % 2^256
  (uint.sub_mod.Uint.sub_mod hi lo P) ⦃ r =>
    uintVal hi < uintVal P ∧ uintVal lo < uintVal P ∧
    expected < uintVal P ∧ uintVal r < uintVal P ∧ expected = uintVal r ⦄

/-- PBT `wrapping_or` (tests/uint.rs:475-483):
```
fn wrapping_or(a in uint(), b in uint()) {
    let expected = to_uint(a_bi | b_bi);
    let actual = a.wrapping_or(&b);
    prop_assert_eq!(expected, actual);
}
```
`BigUint`'s `|` is `Nat.lor` (`|||`) on the values. -/
def wrapping_or_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  (uint.bit_or.Uint.wrapping_or a b) ⦃ r => uintVal r = (uintVal a ||| uintVal b) % 2^256 ⦄

/-- PBT `wrapping_and` (tests/uint.rs:485-493):
```
fn wrapping_and(a in uint(), b in uint()) {
    let expected = to_uint(a_bi & b_bi);
    let actual = a.wrapping_and(&b);
    prop_assert_eq!(expected, actual);
}
```
`BigUint`'s `&` is `Nat.land` (`&&&`) on the values. -/
def wrapping_and_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  (uint.bit_and.Uint.wrapping_and a b) ⦃ r => uintVal r = (uintVal a &&& uintVal b) % 2^256 ⦄

/-- PBT `wrapping_xor` (tests/uint.rs:495-503):
```
fn wrapping_xor(a in uint(), b in uint()) {
    let expected = to_uint(a_bi ^ b_bi);
    let actual = a.wrapping_xor(&b);
    prop_assert_eq!(expected, actual);
}
```
`BigUint`'s `^` is `Nat.xor` (`^^^`) on the values. -/
def wrapping_xor_matches_biguint_spec (a b : uint.Uint 4#usize) : Prop :=
  (uint.bit_xor.Uint.wrapping_xor a b) ⦃ r => uintVal r = (uintVal a ^^^ uintVal b) % 2^256 ⦄

axiom le_bytes_roundtrip (a : uint.Uint 4#usize) :
    le_bytes_roundtrip_spec a

axiom wrapping_add_matches_biguint (a b : uint.Uint 4#usize) :
    wrapping_add_matches_biguint_spec a b

axiom wrapping_and_matches_biguint (a b : uint.Uint 4#usize) :
    wrapping_and_matches_biguint_spec a b

axiom wrapping_sub_matches_biguint (a b : uint.Uint 4#usize) :
    wrapping_sub_matches_biguint_spec a b

axiom wrapping_xor_matches_biguint (a b : uint.Uint 4#usize) :
    wrapping_xor_matches_biguint_spec a b

end Benchmark.Cases.CryptoBigint.Uint.Oracle
