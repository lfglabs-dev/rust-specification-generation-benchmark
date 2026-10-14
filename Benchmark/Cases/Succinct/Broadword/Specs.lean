import Benchmark.Cases.Succinct.Broadword.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open succinct
open Benchmark.Cases.Succinct.Broadword

namespace Benchmark.Cases.Succinct.Broadword.Oracle

/-- PBT `broadword::test::count_ones_qc` (src/broadword.rs:151-154), property
`count_ones_prop` (src/broadword.rs:143-145):
`count_ones(word) == word.count_ones() as usize`.
The reference side `u64::count_ones` is executed with its hax CoreModels model
`core.num.U64.count_ones`; the `as usize` cast of the `u32` result preserves the
value, so the returned words are compared through `.val`. -/
def count_ones_matches_std_spec (word : Std.U64) : Prop :=
  (do
    let fast ← broadword.count_ones word
    let reference ← core.num.U64.count_ones word
    ok (fast, reference)) ⦃ r => r.1.val = r.2.val ⦄

/-- PBT `broadword::test::u_nz8_qc` (src/broadword.rs:233-236), property
`u_nz8_prop` (src/broadword.rs:219-231):
```
let n = hash(&(n0, n1, n2, n3));
let r = u_nz8(n);
for i in 0..8 {
    let ni = n.get_bits(8 * i, 8);
    let ri = r.get_bits(8 * i, 8);
    if (ni != 0) != (ri == 0x80) { return false; }
}
true
```
The generated tuple is only hashed to obtain a well-spread word `n`; the
property is stated for every word `n` (see translation notes). -/
def u_nz8_bytewise_spec (n : Std.U64) : Prop :=
  broadword.u_nz8 n ⦃ r => ∀ i, i < 8 → (byteAt n i ≠ 0 ↔ byteAt r i = 0x80) ⦄

/-- PBT `broadword::test::u_le8_qc` (src/broadword.rs:320-323), property
`u_le8_prop` (src/broadword.rs:306-318):
```
let r = u_le8(n, m);
for i in 0..8 {
    let ni = n.get_bits(8 * i, 8);
    let mi = m.get_bits(8 * i, 8);
    let ri = r.get_bits(8 * i, 8);
    if (ni <= mi) != (ri == 0x80) { return false; }
}
true
``` -/
def u_le8_bytewise_spec (n m : Std.U64) : Prop :=
  broadword.u_le8 n m ⦃ r => ∀ i, i < 8 → (byteAt n i ≤ byteAt m i ↔ byteAt r i = 0x80) ⦄

axiom count_ones_matches_std (word : Std.U64) :
    count_ones_matches_std_spec word

axiom u_le8_bytewise (n m : Std.U64) :
    u_le8_bytewise_spec n m

axiom u_nz8_bytewise (n : Std.U64) :
    u_nz8_bytewise_spec n

end Benchmark.Cases.Succinct.Broadword.Oracle
