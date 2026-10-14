import Benchmark.Cases.IndexedBitvec.Word.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open indexed_bitvec_core
open Benchmark.Cases.IndexedBitvec.Word

namespace Benchmark.Cases.IndexedBitvec.Word.Oracle

/-- PBT `tests::test_ceil_div` (core/src/lib.rs:123-126):
`prop_assert_eq!(ceil_div_slow(x, d), ceil_div(x, d))` — the wrapping fast path
agrees with the reference `n / d + (n % d > 0)` (both sides are Rust calls,
evaluated left to right). -/
def ceil_div_matches_slow_spec (x d : Std.Usize) : Prop :=
  (do
    let slow ← ceil_div_slow x d
    let fast ← ceil_div x d
    ok (slow, fast)) ⦃ (slow, fast) => slow = fast ⦄

/-- PBT `tests::test_ceil_div_64` (core/src/lib.rs:128-131):
`prop_assert_eq!(ceil_div_u64_slow(x, d), ceil_div_u64(x, d))`. -/
def ceil_div_u64_matches_slow_spec (x d : Std.U64) : Prop :=
  (do
    let slow ← ceil_div_u64_slow x d
    let fast ← ceil_div_u64 x d
    ok (slow, fast)) ⦃ (slow, fast) => slow = fast ⦄

/-- PBT `word::tests::test_set` (core/src/word.rs:261-284), quickcheck
`fn test_set(x: Word) -> bool`:
```
(0..x.len()).all(|i| {
    let set_true = { let mut x = x.clone(); x.set(i, true).unwrap(); x };
    let set_false = { let mut x = x.clone(); x.set(i, false).unwrap(); x };
    (0..x.len()).all(|j| {
        if i == j { set_true.get(j).unwrap() == true && set_false.get(j).unwrap() == false }
        else { set_true.get(j) == x.get(j) && set_false.get(j) == x.get(j) }
    })
})
```
The test returns `true` iff every inner check holds without panicking; this is
stated for every pair `i, j < 64`. `Word::set` takes `&mut self`; Aeneas returns
its result together with the updated word (`(Option<()>, Word)`), and
`.unwrap()` succeeds iff the result is `Some(())`. `get(j).unwrap() == b` holds
iff `get(j)` returns `Some(b)`. -/
def set_updates_only_target_bit_spec (x : word.Word) : Prop :=
  ∀ i j : Std.Usize, i.val < 64 → j.val < 64 →
    (do
      let (rt, set_true) ← word.Word.set x i true
      let (rf, set_false) ← word.Word.set x i false
      let gt ← word.Word.get set_true j
      let gf ← word.Word.get set_false j
      let g ← word.Word.get x j
      ok (rt, rf, gt, gf, g)) ⦃ (rt, rf, gt, gf, g) =>
        rt = core.option.Option.Some () ∧ rf = core.option.Option.Some () ∧
        (if i = j then
          gt = core.option.Option.Some true ∧ gf = core.option.Option.Some false
        else gt = g ∧ gf = g) ⦄

/-- PBT `word::tests::test_complement` (core/src/word.rs:292-295), quickcheck
`fn test_complement(x: Word) -> bool`:
```
let y = x.complement();
(0..x.len()).all(|i| x.get(i) != y.get(i))
```
-/
def complement_flips_every_bit_spec (x : word.Word) : Prop :=
  word.Word.complement x ⦃ y =>
    ∀ i : Std.Usize, i.val < 64 →
      (do
        let a ← word.Word.get x i
        let b ← word.Word.get y i
        ok (a, b)) ⦃ (a, b) => a ≠ b ⦄ ⦄

/-- PBT `word::tests::test_rank` (core/src/word.rs:307-321), quickcheck
`fn test_rank(x: Word) -> ()`:
```
let mut expected_rank_ones = 0u32;
let mut expected_rank_zeros = 0u32;
for i in 0..x.len() {
    assert_eq!(Some(expected_rank_ones), x.rank_ones(i));
    assert_eq!(Some(expected_rank_zeros), x.rank_zeros(i));
    if x.get(i).unwrap() { expected_rank_ones += 1; } else { expected_rank_zeros += 1; }
}
assert_eq!(None, x.rank_ones(x.len()));
assert_eq!(None, x.rank_zeros(x.len()));
```
The running counters are the naive counts of the bits reported by
`x.get(j).unwrap()` for `j < i` (`GetBits`, `countBits`); they never exceed 64,
so the test's `+= 1` on `u32` cannot overflow. -/
def rank_matches_get_count_spec (x : word.Word) : Prop :=
  ∃ bit : Nat → Bool, GetBits x bit ∧
    (∀ i : Std.Usize, i.val < 64 →
      (do
        let ones ← word.Word.rank_ones x i
        let zeros ← word.Word.rank_zeros x i
        ok (ones, zeros)) ⦃ (ones, zeros) =>
          (∃ e : Std.U32, ones = core.option.Option.Some e ∧ e.val = countBits bit true i.val) ∧
          (∃ e : Std.U32, zeros = core.option.Option.Some e ∧ e.val = countBits bit false i.val) ⦄) ∧
    word.Word.rank_ones x 64#usize ⦃ r => r = core.option.Option.None ⦄ ∧
    word.Word.rank_zeros x 64#usize ⦃ r => r = core.option.Option.None ⦄

/-- PBT `word::tests::test_select_u16` (core/src/word.rs:323-334), quickcheck
`fn test_select_u16(x: u16) -> ()`:
```
let total_count = x.count_ones() as usize;
let x_bits = Word::from((x as u64) << 48);
for i in 0..total_count {
    let r = select_ones_u16(x, i as u32) as usize;
    let prev_rank = (0..r).filter(|&j| x_bits.get(j).unwrap()).count();
    assert_eq!(prev_rank, i);
    assert!(x_bits.get(r).unwrap());
}
assert_eq!(select_ones_u16(x, total_count as u32), 16);
assert_eq!(select_ones_u16(x, 16), 16);
```
`total_count` comes from the CoreModels model of `u16::count_ones`; the casts
`u32 → usize → u32` are lossless (`total_count ≤ 16`), so the loop index is
quantified directly as a `u32` below `total`. The loop body calls
`x_bits.get(j).unwrap()` for every `j ≤ r`, which succeeds iff `r < 64`
(`get` returns `None` from index 64 on); given that, `prev_rank` is the naive
count of the bits reported by `get` (`GetBits`, `countBits`). -/
def select_ones_u16_matches_rank_spec (x : Std.U16) : Prop :=
  (do
    let total ← core.num.U16.count_ones x
    let wide ← lift (UScalar.cast .U64 x)
    let shifted ← wide <<< 48#i32
    let x_bits ← word.Word.Insts.CoreConvertFromU64.from shifted
    ok (total, x_bits)) ⦃ (total, x_bits) =>
      ∃ bit : Nat → Bool, GetBits x_bits bit ∧
        (∀ i : Std.U32, i.val < total.val →
          word.select_ones_u16 x i ⦃ r =>
            r.val < 64 ∧ countBits bit true r.val = i.val ∧ bit r.val = true ⦄) ∧
        word.select_ones_u16 x total ⦃ r => r.val = 16 ⦄ ∧
        word.select_ones_u16 x 16#u32 ⦃ r => r.val = 16 ⦄ ⦄

/-- PBT `word::tests::test_select_ones` (core/src/word.rs:336-344), quickcheck
`fn test_select_ones(x: Word) -> ()`:
```
let total_count = x.count_ones() as usize;
for i in 0..total_count {
    let r = x.select_ones(i as u32).unwrap() as usize;
    assert_eq!(Some(i as u32), x.rank_ones(r));
    assert_eq!(Some(true), x.get(r));
}
assert_eq!(None, x.select_ones(total_count as u32));
```
`total_count ≤ 64`, so the casts `u32 → usize → u32` of the loop index and of
`total_count` are lossless; the loop index is quantified as a `u32` below
`total`. The `u32 → usize` cast of the selected position is the extracted
primitive cast. -/
def select_ones_inverts_rank_spec (x : word.Word) : Prop :=
  word.Word.count_ones x ⦃ total =>
    (∀ i : Std.U32, i.val < total.val →
      (do
        let o ← word.Word.select_ones x i
        let r ← core.option.Option.unwrap o
        let r ← lift (UScalar.cast .Usize r)
        let rank ← word.Word.rank_ones x r
        let g ← word.Word.get x r
        ok (rank, g)) ⦃ (rank, g) =>
          rank = core.option.Option.Some i ∧ g = core.option.Option.Some true ⦄) ∧
    word.Word.select_ones x total ⦃ o => o = core.option.Option.None ⦄ ⦄

axiom ceil_div_matches_slow (x d : Std.Usize)
    (h_d_lo : 1 ≤ d.val) (h_d_hi : d.val < 999999) :
    ceil_div_matches_slow_spec x d

axiom ceil_div_u64_matches_slow (x d : Std.U64)
    (h_d_lo : 1 ≤ d.val) (h_d_hi : d.val < 999999) :
    ceil_div_u64_matches_slow_spec x d

axiom select_ones_inverts_rank (x : word.Word) :
    select_ones_inverts_rank_spec x

axiom set_updates_only_target_bit (x : word.Word) :
    set_updates_only_target_bit_spec x

end Benchmark.Cases.IndexedBitvec.Word.Oracle
