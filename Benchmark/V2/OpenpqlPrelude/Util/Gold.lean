import Benchmark.V2.Prelude
import OpenpqlPreludeUtil.Extraction

/-! Hidden gold specification for target `openpql_prelude/util`.

API: `iterator::binomial::coefficient::binom`, `waugh_indexer::util::{suffix_product,
dot_product, const_sort}`, `waugh_indexer::mixed_radix::MixedRadix::{new, size,
encode, decode}`.

Contract notes (true to the implementation):
* `binom n r` = `C(n, r)` (0 for `r > n`); `debug_assert!(n <= 52)` panics for `n > 52`.
* `suffix_product` replaces entry `i` by the product of the entries after `i`, but its
  accumulator also multiplies in the *first* entry, so it panics as soon as any suffix
  product (including the product of the whole slice) overflows `u64` — even when every
  stored output fits (latent bug; a sibling that skips the last multiplication is
  registered, and the gold spec accepts a panic or the correct output in that case).
  Consequently `MixedRadix::new` panics iff the product of all block sizes overflows
  (e.g. `[65536; 4]`); with the sibling, `new` succeeds and `size` panics instead.
* `dot_product` panics iff the exact dot product is `≥ 2^64`.
* `decode` panics (division by zero) iff some block size other than the first is 0;
  it does not reduce the leading digit modulo `block_sizes[0]` (for indices `≥ size`
  the leading digit is treated as unspecified; a reducing sibling is registered).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM openpql_prelude RSGB

/-! Data-valued helpers (outside `Benchmark.` so the driver does not unfold them). -/
namespace RSGBGold.OpenpqlPreludeUtil

def vals (l : List Std.U64) : List Nat := l.map (·.val)

def widenA {ty : UScalarTy} {n : Std.Usize} (a : Std.Array (UScalar ty) n) : Std.Array Std.U64 n :=
  ⟨a.val.map (fun x => mkU .U64 x.val), by simp [a.property]⟩

/-- Block sizes `b + 1` (all ≥ 1). -/
def bumpA {ty : UScalarTy} {n : Std.Usize} (a : Std.Array (UScalar ty) n) : Std.Array Std.U64 n :=
  ⟨a.val.map (fun x => mkU .U64 (x.val + 1)), by simp [a.property]⟩

/-- Digits reduced modulo the block sizes. -/
def digitsMod {n : Std.Usize} (d bs : Std.Array Std.U64 n) : Std.Array Std.U64 n :=
  ⟨List.zipWith (fun x b => mkU .U64 (x.val % b.val)) d.val bs.val, by simp [d.property, bs.property]⟩

def widenS {ty : UScalarTy} (s : Slice (UScalar ty)) : Slice Std.U64 :=
  ⟨s.val.map (fun x => mkU .U64 x.val), by simpa using s.property⟩

/-- `C(n, r)` (Mathlib `Nat.choose`, which is 0 for `r > n`). -/
def binomExp (n r : Nat) : RustM Nat :=
  if n > 52 then fail .panic else ok (Nat.choose n r)

/-- Entry `i` ↦ product of the entries strictly after `i`. -/
def sufProds (l : List Nat) : List Nat :=
  (List.range l.length).map (fun i => (l.drop (i + 1)).prod)

/-- Some suffix `l[i..]` (including the whole list) has product `≥ 2^64`. -/
def sufOverflow (l : List Nat) : Bool :=
  (List.range l.length).any (fun i => decide (2^64 ≤ (l.drop i).prod))

/-- Some *stored* suffix product `l[i..]`, `i ≥ 1`, overflows. -/
def sufOverflowStored (l : List Nat) : Bool := sufOverflow l.tail

/-- Acceptable outcomes of `suffix_product`: the suffix products; a panic when a stored
product overflows; when only the product of the whole slice overflows (it is computed
by the implementation's accumulator but never stored) a panic or the correct output. -/
def suffixOk (l : List Nat) : RustM (List Nat) → Bool
  | .ok r => !sufOverflowStored l && r == sufProds l
  | .fail .panic => sufOverflow l
  | _ => false

def dotExp (a b : List Nat) : RustM Nat :=
  let s := (List.zipWith (· * ·) a b).sum
  if 2^64 ≤ s then fail .panic else ok s

def sortExp (l : List Nat) : List Nat := l.mergeSort (fun a b => decide (a ≤ b))

/-- Observable state of a `MixedRadix`: `(block_sizes, size)`; `size` itself may panic. -/
def newExp (bs : List Nat) : RustM (List Nat × Nat) :=
  if sufOverflow bs then fail .panic
  else if bs = [] then fail .panic
  else ok (bs, bs.prod)

/-- `encode`: `Σ dᵢ · ∏_{j>i} bⱼ`, panicking on `u64` overflow. -/
def encodeExp (bs d : List Nat) : RustM Nat := dotExp d (sufProds bs)

/-- Acceptable outcomes of `decode`: digit `i ≥ 1` is `(idx / ∏_{j>i} bⱼ) mod bᵢ`; digit 0
is `idx / ∏_{j>0} bⱼ` when `idx < ∏ bᵢ` (for out-of-range indices the leading digit is
left unspecified); panics (division by zero) exactly when some trailing block size is 0. -/
def decodeOk (bs : List Nat) (idx : Nat) : RustM (List Nat) → Bool
  | .ok r =>
    let offs := sufProds bs
    !(offs.any (· == 0)) && r.length == bs.length &&
    r.tail == ((List.range bs.length).map (fun i => (idx / offs.getD i 1) % bs.getD i 1)).tail &&
    (decide (bs.prod ≤ idx) || r.head? == (offs.head?.map (fun o => idx / o)))
  | .fail .panic => (sufProds bs).any (· == 0)
  | _ => false

def mrObs {n : Std.Usize} (bs : Std.Array Std.U64 n) : RustM (List Nat × Nat) := do
  let m ← waugh_indexer.mixed_radix.MixedRadix.new bs
  let s ← waugh_indexer.mixed_radix.MixedRadix.size m
  ok (vals m.block_sizes.val, s.val)

def encodeObs {n : Std.Usize} (bs d : Std.Array Std.U64 n) : RustM Nat := do
  let m ← waugh_indexer.mixed_radix.MixedRadix.new bs
  let e ← waugh_indexer.mixed_radix.MixedRadix.encode m d
  ok e.val

def decodeObs {n : Std.Usize} (bs : Std.Array Std.U64 n) (idx : Std.U64) : RustM (List Nat) := do
  let m ← waugh_indexer.mixed_radix.MixedRadix.new bs
  let d ← waugh_indexer.mixed_radix.MixedRadix.decode m idx
  ok (vals d.val)

def suffixObs (s : Slice Std.U64) : RustM (List Nat) := do
  let r ← waugh_indexer.util.suffix_product s
  ok (vals r.val)

def sortObs {n : Std.Usize} (a : Std.Array Std.U64 n) : RustM (List Nat) := do
  let r ← waugh_indexer.util.const_sort a
  ok (vals r.val)

def dotObs {n : Std.Usize} (a b : Std.Array Std.U64 n) : RustM Nat := do
  let r ← waugh_indexer.util.dot_product a b
  ok r.val

def binomObs (n r : Nat) : RustM Nat := do
  let x ← iterator.binomial.coefficient.binom (mkU .Usize n) (mkU .Usize r)
  ok x.val

/-- Second argument choice that keeps `binom` loops short even without the `n ≤ 52` check. -/
def shortR (n : Nat) (r : Nat) : Nat :=
  if r < 100 then r % 4 else if r < 200 then n - r % 4 else n + 1 + r

end RSGBGold.OpenpqlPreludeUtil

namespace Benchmark.V2.OpenpqlPrelude.Util.Gold
open RSGBGold.OpenpqlPreludeUtil

/-! ## binom -/

/-- `binom n r = C(n, r)` for `n ≤ 52` (0 when `r > n`), panic for `n > 52` (dense). -/
def gold_binom_exact (n r : Std.U8) : Prop :=
  binomObs (n.val % 64) (r.val % 64) = binomExp (n.val % 64) (r.val % 64)

/-- Same on the full `u8` square. -/
def gold_binom_exact_u8 (n r : Std.U8) : Prop :=
  binomObs n.val r.val = binomExp n.val r.val

/-- `binom n r` panics for every `n > 52` (arbitrary `usize`). -/
def gold_binom_panics (n : Std.Usize) (r : Std.U8) : Prop :=
  52 < n.val →
    iterator.binomial.coefficient.binom n (mkU .Usize (shortR n.val r.val)) = fail .panic

/-- `r > n` gives 0 (for any `usize` `r`) when `n ≤ 52`. -/
def gold_binom_r_gt_n (n : Std.U8) (r : Std.Usize) : Prop :=
  n.val % 53 < r.val → binomObs (n.val % 53) r.val = ok 0

/-- Pascal's rule. -/
def gold_binom_pascal (n r : Std.U8) : Prop :=
  let n' := n.val % 52 + 1
  let r' := r.val % 54 + 1
  (do
    let a ← binomObs n' r'
    let b ← binomObs (n' - 1) (r' - 1)
    let c ← binomObs (n' - 1) r'
    ok (a, b + c)) ⦃ p => p.1 = p.2 ⦄

/-- Symmetry `C(n, r) = C(n, n - r)`. -/
def gold_binom_symm (n r : Std.U8) : Prop :=
  let n' := n.val % 53
  let r' := r.val % (n' + 1)
  binomObs n' r' = binomObs n' (n' - r')

/-! ## suffix_product -/

/-- Exact: suffix products, panicking iff some suffix product (incl. the whole slice) overflows. -/
def gold_suffix_exact_u8 (s : Slice Std.U8) : Prop :=
  suffixOk (s.val.map (·.val)) (suffixObs (widenS s)) = true

def gold_suffix_exact_u16 (s : Slice Std.U16) : Prop :=
  suffixOk (s.val.map (·.val)) (suffixObs (widenS s)) = true

def gold_suffix_exact_u64 (s : Slice Std.U64) : Prop :=
  suffixOk (vals s.val) (suffixObs s) = true

/-- Short slices of small values (frequent zeros/ones, no overflow). -/
def gold_suffix_exact_small (s : Slice Std.U8) : Prop :=
  let t : Slice Std.U64 := ⟨s.val.map (fun x => mkU .U64 (x.val % 5)), by simpa using s.property⟩
  suffixOk (s.val.map (·.val % 5)) (suffixObs t) = true

/-- Length preserved and last entry 1 whenever it succeeds. -/
def gold_suffix_shape (s : Slice Std.U32) : Prop :=
  ¬ sufOverflow (s.val.map (·.val)) →
    (suffixObs (widenS s)) ⦃ r => r.length = s.val.length ∧ (r ≠ [] → r.getLast? = some 1) ⦄

/-! ## dot_product -/

def gold_dot_exact_u16 (a b : Std.Array Std.U16 4#usize) : Prop :=
  dotObs (widenA a) (widenA b) = dotExp (a.val.map (·.val)) (b.val.map (·.val))

def gold_dot_exact_u32 (a b : Std.Array Std.U32 3#usize) : Prop :=
  dotObs (widenA a) (widenA b) = dotExp (a.val.map (·.val)) (b.val.map (·.val))

def gold_dot_exact_u64 (a b : Std.Array Std.U64 4#usize) : Prop :=
  dotObs a b = dotExp (vals a.val) (vals b.val)

def gold_dot_exact_len1 (a b : Std.Array Std.U64 1#usize) : Prop :=
  dotObs a b = dotExp (vals a.val) (vals b.val)

def gold_dot_empty (a b : Std.Array Std.U64 0#usize) : Prop :=
  dotObs a b = ok 0

def gold_dot_comm (a b : Std.Array Std.U32 5#usize) : Prop :=
  dotObs (widenA a) (widenA b) = dotObs (widenA b) (widenA a)

/-! ## const_sort -/

def gold_sort_10 (a : Std.Array Std.U64 10#usize) : Prop :=
  sortObs a = ok (sortExp (vals a.val))

/-- Many duplicates. -/
def gold_sort_10_dups (a : Std.Array Std.U8 10#usize) : Prop :=
  let b : Std.Array Std.U64 10#usize :=
    ⟨a.val.map (fun x => mkU .U64 (x.val % 4)), by simp [a.property]⟩
  sortObs b = ok (sortExp (a.val.map (·.val % 4)))

def gold_sort_3 (a : Std.Array Std.U16 3#usize) : Prop :=
  sortObs (widenA a) = ok (sortExp (a.val.map (·.val)))

def gold_sort_1 (a : Std.Array Std.U64 1#usize) : Prop :=
  sortObs a = ok (vals a.val)

def gold_sort_0 (a : Std.Array Std.U64 0#usize) : Prop :=
  sortObs a = ok []

/-! ## MixedRadix -/

/-- `new` keeps the block sizes; `size` is their product (u16 sizes, no overflow). -/
def gold_mr_new_size (bs : Std.Array Std.U16 4#usize) : Prop :=
  mrObs (widenA bs) = newExp (bs.val.map (·.val))

/-- `new` panics iff some suffix product of the block sizes overflows (u32 sizes). -/
def gold_mr_new_overflow3 (bs : Std.Array Std.U32 3#usize) : Prop :=
  mrObs (widenA bs) = newExp (bs.val.map (·.val))

def gold_mr_new_overflow4 (bs : Std.Array Std.U64 4#usize) : Prop :=
  mrObs bs = newExp (vals bs.val)

/-- `N = 0`: `new` succeeds, `size` panics (index 0 out of bounds), `encode` is 0,
`decode` is empty. -/
def gold_mr_empty (bs d : Std.Array Std.U64 0#usize) (idx : Std.U64) : Prop :=
  mrObs bs = fail .panic ∧ encodeObs bs d = ok 0 ∧ decodeObs bs idx = ok []

/-- `encode` is the mixed-radix value `Σ dᵢ·∏_{j>i} bⱼ` (panics on overflow). -/
def gold_mr_encode (bs : Std.Array Std.U16 4#usize) (d : Std.Array Std.U16 4#usize) : Prop :=
  encodeObs (widenA bs) (widenA d) = encodeExp (bs.val.map (·.val)) (d.val.map (·.val))

def gold_mr_encode_u64 (bs : Std.Array Std.U8 4#usize) (d : Std.Array Std.U64 4#usize) : Prop :=
  encodeObs (widenA bs) d = encodeExp (bs.val.map (·.val)) (vals d.val)

/-- `decode` model (incl. division-by-zero panic when a trailing block size is 0). -/
def gold_mr_decode (bs : Std.Array Std.U8 4#usize) (idx : Std.U64) : Prop :=
  decodeOk (bs.val.map (·.val)) idx.val (decodeObs (widenA bs) idx) = true

def gold_mr_decode_u16 (bs : Std.Array Std.U16 4#usize) (idx : Std.U64) : Prop :=
  decodeOk (bs.val.map (·.val)) idx.val (decodeObs (widenA bs) idx) = true

def gold_mr_decode_3 (bs : Std.Array Std.U8 3#usize) (idx : Std.U16) : Prop :=
  decodeOk (bs.val.map (·.val + 1)) idx.val (decodeObs (bumpA bs) (mkU .U64 idx.val)) = true

/-- Round trip `decode (encode d) = d` for valid digits (upstream property, all sizes ≥ 1). -/
def gold_mr_roundtrip (bs d : Std.Array Std.U16 4#usize) : Prop :=
  let b := bumpA bs
  let ds := digitsMod (widenA d) b
  (do
    let m ← waugh_indexer.mixed_radix.MixedRadix.new b
    let e ← waugh_indexer.mixed_radix.MixedRadix.encode m ds
    let r ← waugh_indexer.mixed_radix.MixedRadix.decode m e
    ok r) ⦃ r => vals r.val = vals ds.val ⦄

/-- Round trip `encode (decode i) = i` and the decoded digits are in range, for `i < size`. -/
def gold_mr_roundtrip_inv (bs : Std.Array Std.U8 4#usize) (idx : Std.U64) : Prop :=
  let b := bumpA bs
  (do
    let m ← waugh_indexer.mixed_radix.MixedRadix.new b
    let s ← waugh_indexer.mixed_radix.MixedRadix.size m
    let i := mkU .U64 (idx.val % s.val)
    let r ← waugh_indexer.mixed_radix.MixedRadix.decode m i
    let e ← waugh_indexer.mixed_radix.MixedRadix.encode m r
    ok (i, r, e)) ⦃ (i, r, e) =>
      e = i ∧ (List.zipWith (fun x y => decide (x.val < y.val)) r.val b.val).all id ⦄

/-! Differential-testing probes. -/

def diff_binom (n r : Std.U8) := binomObs (n.val % 64) (r.val % 64)
def diff_binom_big (n : Std.Usize) (r : Std.U8) :=
  iterator.binomial.coefficient.binom n (mkU .Usize (shortR n.val r.val))
def diff_suffix_u8 (s : Slice Std.U8) := suffixObs (widenS s)
def diff_suffix_u16 (s : Slice Std.U16) := suffixObs (widenS s)
def diff_suffix_u64 (s : Slice Std.U64) := suffixObs s
def diff_dot_u16 (a b : Std.Array Std.U16 4#usize) := dotObs (widenA a) (widenA b)
def diff_dot_u32 (a b : Std.Array Std.U32 3#usize) := dotObs (widenA a) (widenA b)
def diff_dot_u64 (a b : Std.Array Std.U64 4#usize) := dotObs a b
def diff_sort_10 (a : Std.Array Std.U64 10#usize) := sortObs a
def diff_sort_dups (a : Std.Array Std.U8 10#usize) :=
  sortObs (⟨a.val.map (fun x => mkU .U64 (x.val % 4)), by simp [a.property]⟩ : Std.Array Std.U64 10#usize)
def diff_sort_3 (a : Std.Array Std.U16 3#usize) := sortObs (widenA a)
def diff_mr_new (bs : Std.Array Std.U16 4#usize) := mrObs (widenA bs)
def diff_mr_new3 (bs : Std.Array Std.U32 3#usize) := mrObs (widenA bs)
def diff_mr_encode (bs d : Std.Array Std.U16 4#usize) := encodeObs (widenA bs) (widenA d)
def diff_mr_decode (bs : Std.Array Std.U8 4#usize) (idx : Std.U64) := decodeObs (widenA bs) idx
def diff_mr_decode_small (bs : Std.Array Std.U8 3#usize) (idx : Std.U16) :=
  decodeObs (bumpA bs) (mkU .U64 idx.val)
def diff_mr_empty (bs d : Std.Array Std.U64 0#usize) (idx : Std.U64) :=
  (mrObs bs, encodeObs bs d, decodeObs bs idx)

end Benchmark.V2.OpenpqlPrelude.Util.Gold
