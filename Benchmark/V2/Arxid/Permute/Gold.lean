import Benchmark.V2.Prelude
import ArxidPermute.Extraction

/-! Hidden gold specification for target `arxid/permute`. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM arxid RSGB

namespace Benchmark.V2.Arxid.Permute.Gold

/-- `obfuscate` never panics and stays in the 40-bit domain. -/
def gold_obf_total_domain (id key : Std.U64) : Prop :=
  permute.obfuscate id key ⦃ c => c.val < 2^40 ⦄

/-- `deobfuscate` never panics and stays in the 40-bit domain. -/
def gold_deobf_total_domain (code key : Std.U64) : Prop :=
  permute.deobfuscate code key ⦃ c => c.val < 2^40 ⦄

/-- Bits above the domain are ignored by `obfuscate`. -/
def gold_obf_masks (id key : Std.U64) : Prop :=
  permute.obfuscate id key = permute.obfuscate (mkU .U64 (id.val % 2^40)) key

/-- Bits above the domain are ignored by `deobfuscate`. -/
def gold_deobf_masks (code key : Std.U64) : Prop :=
  permute.deobfuscate code key = permute.deobfuscate (mkU .U64 (code.val % 2^40)) key

/-- `deobfuscate ∘ obfuscate` is the identity on the domain. -/
def gold_roundtrip (id key : Std.U64) : Prop :=
  id.val < 2^40 →
    (do let c ← permute.obfuscate id key; permute.deobfuscate c key) ⦃ r => r = id ⦄

/-- `obfuscate ∘ deobfuscate` is the identity on the domain (permutation). -/
def gold_roundtrip_inv (code key : Std.U64) : Prop :=
  code.val < 2^40 →
    (do let i ← permute.deobfuscate code key; permute.obfuscate i key) ⦃ r => r = code ⦄

/-- `obfuscate` is `feistel_n` at `(ROUNDS, WIDTH_BITS) = (6, 40)` on the masked input. -/
def gold_obf_is_feistel (id key : Std.U64) : Prop :=
  permute.obfuscate id key = permute.feistel_n (mkU .U64 (id.val % 2^40)) key 6#usize 40#u32

/-- `deobfuscate` is `feistel_n_inv` at `(6, 40)` on the masked input. -/
def gold_deobf_is_feistel_inv (code key : Std.U64) : Prop :=
  permute.deobfuscate code key = permute.feistel_n_inv (mkU .U64 (code.val % 2^40)) key 6#usize 40#u32

/-- For `width < 64`, `feistel_n` is total, its output fits in `2*(width/2)` bits,
and `feistel_n_inv` inverts it on the bits it keeps. -/
def gold_feistel_inverse (x key : Std.U64) (r w : Std.U8) : Prop :=
  r.val ≤ 24 → w.val < 64 →
    (do
      let y ← permute.feistel_n x key (mkU .Usize r.val) (mkU .U32 w.val)
      let z ← permute.feistel_n_inv y key (mkU .Usize r.val) (mkU .U32 w.val)
      ok (y, z)) ⦃ (y, z) => y.val < 2^(2 * (w.val / 2)) ∧ z.val = x.val % 2^(2 * (w.val / 2)) ⦄

/-- `feistel_n_inv ∘ … ` the other way round. -/
def gold_feistel_inverse' (x key : Std.U64) (r w : Std.U8) : Prop :=
  r.val ≤ 24 → w.val < 64 →
    (do
      let y ← permute.feistel_n_inv x key (mkU .Usize r.val) (mkU .U32 w.val)
      let z ← permute.feistel_n y key (mkU .Usize r.val) (mkU .U32 w.val)
      ok (y, z)) ⦃ (y, z) => y.val < 2^(2 * (w.val / 2)) ∧ z.val = x.val % 2^(2 * (w.val / 2)) ⦄

/-- With at least one round, a width of 64 bits or more panics (the round
function shifts a `u32` by `width / 2 ≥ 32`), for both directions. -/
def gold_feistel_panics (x key : Std.U64) (r w : Std.U8) : Prop :=
  1 ≤ r.val → r.val ≤ 24 → 64 ≤ w.val →
    permute.feistel_n x key (mkU .Usize r.val) (mkU .U32 w.val) = fail .panic ∧
    permute.feistel_n_inv x key (mkU .Usize r.val) (mkU .U32 w.val) = fail .panic

/-- The key schedule distinguishes a key from its complement (documented: "all 2^64 keys
are distinct", the spec v1 XOR fold made `key` and `!key` equivalent). -/
def gold_complement_key_differs (key : Std.U64) : Prop :=
  ∃ i < 16, permute.obfuscate (mkU .U64 i) key ≠ permute.obfuscate (mkU .U64 i) (mkU .U64 (2^64 - 1 - key.val))

/-! Differential-testing probes (inputs mapped into the terminating range). -/

def diff_obf (id key : Std.U64) := permute.obfuscate id key
def diff_deobf (code key : Std.U64) := permute.deobfuscate code key
def diff_feistel (x key : Std.U64) (r w : Std.U8) :=
  permute.feistel_n x key (mkU .Usize (r.val % 25)) (mkU .U32 (w.val % 80))
def diff_feistel_inv (x key : Std.U64) (r w : Std.U8) :=
  permute.feistel_n_inv x key (mkU .Usize (r.val % 25)) (mkU .U32 (w.val % 80))

end Benchmark.V2.Arxid.Permute.Gold
