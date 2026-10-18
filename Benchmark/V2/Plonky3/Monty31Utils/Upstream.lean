import Benchmark.Cases.Plonky3.Monty31Utils.Specs
import Benchmark.V2.Plonky3.Monty31Utils.Params

/-! The crate's property tests (v1 oracles) instantiated with the concrete `BB`/`KB`
parameters, so that `baseline` can execute them. -/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM p3_monty_31

namespace Benchmark.V2.Plonky3.Monty31Utils.Upstream
open Benchmark.Cases.Plonky3.Monty31Utils.Oracle

def bb_add_sub_roundtrip (a b : Std.U32) : Prop :=
  a.val < 2013265921 → b.val < 2013265921 → bb_add_sub_roundtrip_spec RSGB.Monty31.BB a b

def bb_from_to_monty_roundtrip (m : Std.U32) : Prop :=
  m.val < 2013265921 → bb_from_to_monty_roundtrip_spec RSGB.Monty31.BB m

def bb_large_monty_reduce_identity (x : Std.U64) : Prop :=
  x.val < 2013265921 * 2^32 * 2 → bb_large_monty_reduce_identity_spec RSGB.Monty31.BB x

def bb_monty_reduce_output_range (x : Std.U64) : Prop :=
  x.val < 2013265921 * 2^32 → bb_monty_reduce_output_range_spec RSGB.Monty31.BB x

def bb_monty_reduce_u128_agrees_with_u64 (x : Std.U64) : Prop :=
  x.val < 2013265921 * 2^32 → bb_monty_reduce_u128_agrees_with_u64_spec RSGB.Monty31.BB x

def bb_to_monty_64_extends_32 (x : Std.U32) : Prop :=
  bb_to_monty_64_extends_32_spec RSGB.Monty31.BB x

def kb_add_commutative (a b : Std.U32) : Prop :=
  a.val < 2130706433 → b.val < 2130706433 → kb_add_commutative_spec RSGB.Monty31.KB a b

def kb_large_agrees_with_standard (x : Std.U64) : Prop :=
  x.val < 2130706433 * 2^32 → kb_large_agrees_with_standard_spec RSGB.Monty31.KB x

def kb_large_monty_reduce_output_range (x : Std.U64) : Prop :=
  x.val < 2130706433 * 2^32 * 2 → kb_large_monty_reduce_output_range_spec RSGB.Monty31.KB x

def kb_monty_mul_correct (a b : Std.U32) : Prop :=
  a.val < 2130706433 → b.val < 2130706433 → kb_monty_mul_correct_spec RSGB.Monty31.KB a b

def kb_monty_reduce_identity (x : Std.U64) : Prop :=
  x.val < 2130706433 * 2^32 → kb_monty_reduce_identity_spec RSGB.Monty31.KB x

def kb_monty_reduce_u128_identity (lo : Std.U64) (hi : Std.U32) : Prop :=
  kb_monty_reduce_u128_identity_spec RSGB.Monty31.KB lo hi

def kb_to_from_monty_roundtrip (x : Std.U32) : Prop :=
  x.val < 2130706433 → kb_to_from_monty_roundtrip_spec RSGB.Monty31.KB x

def kb_to_monty_output_range (x : Std.U32) : Prop :=
  kb_to_monty_output_range_spec RSGB.Monty31.KB x

end Benchmark.V2.Plonky3.Monty31Utils.Upstream
