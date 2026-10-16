import Benchmark.V2.Prelude
import Benchmark.Exec.Runtime
import UintU64.Extraction

/-! Hidden gold specification for target `uint/u64`.

`U64` (from `construct_uint! { pub struct U64(1); }`) is a little-endian array
of one `u64` limb; every API function is specified against the mathematical
value of the limb (`v x`), with `Nat` arithmetic as the reference model. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM ethereum_types RSGB

/-! Model and contracts. They live outside the `Benchmark` namespace and are
`Bool`-valued so that the test driver evaluates them instead of unfolding them
symbolically. -/
namespace UintU64GoldModel

abbrev W := uint.U64

/-- Value of a `U64`. -/
def v (x : W) : Nat := (x.val.headD 0#u64).val

/-- The `U64` holding `n mod 2^64`. -/
def ofNat (n : Nat) : W := ⟨[mkU .U64 n], by simp⟩

/-- Least number of bits needed to represent `n`. -/
def bitLen (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- `x + y` / `x - y` with a `U64` right operand, and `x + n` with an `i32` one. -/
def addOp (x y : W) : RustM W :=
  uint.U64.Insts.CoreOpsArithAddTU64.add (core.convert.Into.Blanket (core.convert.From.Blanket uint.U64)) x y
def subOp (x y : W) : RustM W :=
  uint.U64.Insts.CoreOpsArithSubTU64.sub (core.convert.Into.Blanket (core.convert.From.Blanket uint.U64)) x y
def addI32 (x : W) (n : Std.I32) : RustM W :=
  uint.U64.Insts.CoreOpsArithAddTU64.add (core.convert.Into.Blanket uint.U64.Insts.CoreConvertFromI32) x n
def subI32 (x : W) (n : Std.I32) : RustM W :=
  uint.U64.Insts.CoreOpsArithSubTU64.sub (core.convert.Into.Blanket uint.U64.Insts.CoreConvertFromI32) x n

/-- Arithmetic with overflow reporting, checked and panicking variants. -/
def arithSpec (x y : W) : Bool := decide (
  uint.U64.overflowing_add x y = ok (ofNat (v x + v y), decide (2^64 ≤ v x + v y)) ∧
  uint.U64.checked_add x y = ok (if v x + v y < 2^64 then some (ofNat (v x + v y)) else none) ∧
  addOp x y = (if v x + v y < 2^64 then ok (ofNat (v x + v y)) else fail .panic) ∧
  uint.U64.Insts.CoreOpsArithAddAssignU64.add_assign x y =
    (if v x + v y < 2^64 then ok (ofNat (v x + v y)) else fail .panic) ∧
  uint.U64.overflowing_sub x y = ok (ofNat (v x + 2^64 - v y), decide (v x < v y)) ∧
  uint.U64.checked_sub x y = ok (if v y ≤ v x then some (ofNat (v x - v y)) else none) ∧
  subOp x y = (if v y ≤ v x then ok (ofNat (v x - v y)) else fail .panic) ∧
  uint.U64.Insts.CoreOpsArithSubAssignU64.sub_assign x y =
    (if v y ≤ v x then ok (ofNat (v x - v y)) else fail .panic) ∧
  uint.U64.overflowing_neg x = ok (ofNat (2^64 - v x), decide (v x ≠ 0)) ∧
  uint.U64.checked_neg x = ok (if v x = 0 then some x else none))

/-- Bitwise operations and equality. -/
def bitwiseSpec (x y : W) : Bool := decide (
  uint.U64.Insts.CoreOpsBitNotU64.not x = ok (ofNat (2^64 - 1 - v x)) ∧
  uint.U64.Insts.CoreOpsBitBitAndU64U64.bitand x y = ok (ofNat (v x &&& v y)) ∧
  uint.U64.Insts.CoreOpsBitBitOrU64U64.bitor x y = ok (ofNat (v x ||| v y)) ∧
  uint.U64.Insts.CoreOpsBitBitXorU64U64.bitxor x y = ok (ofNat (v x ^^^ v y)) ∧
  uint.U64.Insts.CoreCmpPartialEqU64.eq x y = ok (decide (v x = v y)))

/-- Queries and conversions. -/
def querySpec (x : W) : Bool := decide (
  uint.U64.low_u32 x = ok (mkU .U32 (v x)) ∧
  uint.U64.low_u64 x = ok (mkU .U64 (v x)) ∧
  uint.U64.as_u64 x = ok (mkU .U64 (v x)) ∧
  uint.U64.is_zero x = ok (decide (v x = 0)) ∧
  uint.U64.bits x = ok (mkU .Usize (bitLen (v x))))

/-- `bit i` / `byte i` for an index: the bit / little-endian byte, panicking
exactly when the index exceeds the width. -/
def indexSpec (x : W) (i : Nat) : Bool := decide (
  uint.U64.bit x (mkU .Usize i) = (if i < 64 then ok (Nat.testBit (v x) i) else fail .panic) ∧
  uint.U64.byte x (mkU .Usize i) = (if i < 8 then ok (mkU .U8 (v x / 2^(8 * i))) else fail .panic))

/-- The crate's own laws (associativity / commutativity of `+` when nothing overflows)
plus inverse relations. -/
def lawSpec (x y z : W) : Bool := decide (
  (v x + v y + v z < 2^64 →
    (do let xy ← addOp x y; let l ← addOp xy z; let yz ← addOp y z; let r ← addOp x yz; ok (l, r))
      ⦃ p => p.1 = p.2 ⦄) ∧
  (v x + v y < 2^64 → addOp x y = addOp y x) ∧
  (v y ≤ v x → (do let d ← subOp x y; addOp d y) = ok x) ∧
  (do let (n, _) ← uint.U64.overflowing_neg x; uint.U64.overflowing_add x n) ⦃ p => v p.1 = 0 ∧ p.2 = decide (v x ≠ 0) ⦄)

end UintU64GoldModel

open UintU64GoldModel

namespace Benchmark.V2.Uint.U64.Gold

/-! ## Gold properties -/

def gold_arith (x y : uint.U64) : Prop := arithSpec x y

/-- Arithmetic at the carry / borrow boundary (`y = 2^64 - x + k - 2`, `y = x + k - 2`). -/
def gold_arith_boundary (x : uint.U64) (k : Std.U8) : Prop :=
  arithSpec x (ofNat (2^64 - v x + k.val % 4 - 2)) ∧ arithSpec x (ofNat (v x + k.val % 4 - 2)) ∧
  arithSpec (ofNat (v x + k.val % 4 - 2)) x

def gold_bitwise (x y : uint.U64) : Prop := bitwiseSpec x y ∧ bitwiseSpec x x

def gold_query (x : uint.U64) : Prop := querySpec x

/-- `bits` on single powers of two and their neighbours. -/
def gold_bits_pow (k : Std.U8) : Prop :=
  querySpec (ofNat (2^(k.val % 64))) ∧ querySpec (ofNat (2^(k.val % 64) - 1)) ∧
  querySpec (ofNat (2^(k.val % 64) + 1))

def gold_index (x : uint.U64) (i : Std.U8) : Prop := indexSpec x i.val ∧ indexSpec x (i.val % 72)

/-- `bit` / `byte` right at the width boundary. -/
def gold_index_edges (x : uint.U64) : Prop :=
  ∀ i ∈ [0, 6, 7, 8, 9, 15, 16, 62, 63, 64, 65, 127, 128, 129, 130], indexSpec x i

def gold_index_any (x : uint.U64) (i : Std.Usize) : Prop := indexSpec x i.val

def gold_laws (x y z : uint.U64) : Prop := lawSpec x y z

/-- Constructors: `zero`, `one`, `Default`, and the `From` conversions
(signed ones panic exactly on negative input). -/
def gold_from (n : Std.U64) (m : Std.U32) (a : Std.I64) (b : Std.I32) : Prop :=
  uint.U64.zero = ok (ofNat 0) ∧ uint.U64.one = ok (ofNat 1) ∧
  uint.U64.Insts.CoreDefaultDefault.default = ok (ofNat 0) ∧
  uint.U64.Insts.CoreConvertFromU64.from n = ok (ofNat n.val) ∧
  uint.U64.Insts.CoreConvertFromU32.from m = ok (ofNat m.val) ∧
  uint.U64.Insts.CoreConvertFromI64.from a = (if 0 ≤ a.val then ok (ofNat a.val.toNat) else fail .panic) ∧
  uint.U64.Insts.CoreConvertFromI32.from b = (if 0 ≤ b.val then ok (ofNat b.val.toNat) else fail .panic)

/-- `x + n` / `x - n` with an `i32` right operand: converts (panicking on a
negative `n`) and then adds / subtracts with overflow panic. -/
def gold_add_i32 (x : uint.U64) (n : Std.I32) : Prop :=
  addI32 x n = (if n.val < 0 then fail .panic
    else if v x + n.val.toNat < 2^64 then ok (ofNat (v x + n.val.toNat)) else fail .panic) ∧
  subI32 x n = (if n.val < 0 then fail .panic
    else if n.val.toNat ≤ v x then ok (ofNat (v x - n.val.toNat)) else fail .panic)

/-! ## Differential-testing probes -/

def diff_add (x y : uint.U64) :=
  (uint.U64.overflowing_add x y, uint.U64.checked_add x y, addOp x y,
   uint.U64.Insts.CoreOpsArithAddAssignU64.add_assign x y)
def diff_sub (x y : uint.U64) :=
  (uint.U64.overflowing_sub x y, uint.U64.checked_sub x y, subOp x y,
   uint.U64.Insts.CoreOpsArithSubAssignU64.sub_assign x y)
def diff_neg (x : uint.U64) := (uint.U64.overflowing_neg x, uint.U64.checked_neg x)
def diff_bitwise (x y : uint.U64) :=
  (uint.U64.Insts.CoreOpsBitNotU64.not x, uint.U64.Insts.CoreOpsBitBitAndU64U64.bitand x y,
   uint.U64.Insts.CoreOpsBitBitOrU64U64.bitor x y, uint.U64.Insts.CoreOpsBitBitXorU64U64.bitxor x y,
   uint.U64.Insts.CoreCmpPartialEqU64.eq x y)
def diff_query (x : uint.U64) :=
  (uint.U64.low_u32 x, uint.U64.low_u64 x, uint.U64.as_u64 x, uint.U64.is_zero x, uint.U64.bits x)
def diff_index (x : uint.U64) (i : Std.U8) :=
  (uint.U64.bit x (mkU .Usize i.val), uint.U64.byte x (mkU .Usize (i.val % 32)),
   uint.U64.bit x (mkU .Usize (60 + i.val % 8)), uint.U64.byte x (mkU .Usize (i.val % 12)))
def diff_from (n : Std.U64) (m : Std.U32) (a : Std.I64) (b : Std.I32) :=
  (uint.U64.zero, uint.U64.one, uint.U64.Insts.CoreDefaultDefault.default,
   uint.U64.Insts.CoreConvertFromU64.from n, uint.U64.Insts.CoreConvertFromU32.from m,
   uint.U64.Insts.CoreConvertFromI64.from a, uint.U64.Insts.CoreConvertFromI32.from b)
def diff_i32 (x : uint.U64) (n : Std.I32) := (addI32 x n, subI32 x n)

end Benchmark.V2.Uint.U64.Gold
