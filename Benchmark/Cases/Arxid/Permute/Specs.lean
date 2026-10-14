import Benchmark.Cases.Arxid.Permute.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open arxid
open Benchmark.Cases.Arxid.Permute

namespace Benchmark.Cases.Arxid.Permute.Oracle

/-- PBT `round_trip_over_the_whole_domain` (impl/rust/tests/properties.rs:10):
for `key: u64` and `id in 0u64..=MAX_ID`,
`prop_assert_eq!(deobfuscate(obfuscate(id, key), key), id)`. -/
def round_trip_over_the_whole_domain_spec (key id : Std.U64) : Prop :=
  (do
    let code ← permute.obfuscate id key
    permute.deobfuscate code key) ⦃ back => back = id ⦄

/-- PBT `output_never_leaves_the_domain` (impl/rust/tests/properties.rs:15):
for arbitrary `key: u64` and `id: u64`,
`prop_assert!(obfuscate(id, key) <= MAX_ID)` and then
`prop_assert!(deobfuscate(id, key) <= MAX_ID)` (`MAX_ID = 2^40 - 1`). -/
def output_never_leaves_the_domain_spec (key id : Std.U64) : Prop :=
  (do
    let code ← permute.obfuscate id key
    let back ← permute.deobfuscate id key
    ok (code, back)) ⦃ (code, back) =>
      code.val ≤ 2^40 - 1 ∧ back.val ≤ 2^40 - 1 ⦄

/-- PBT `out_of_domain_input_is_reduced_not_rejected`
(impl/rust/tests/properties.rs:21): for arbitrary `key: u64` and `id: u64`,
`prop_assert_eq!(obfuscate(id, key), obfuscate(id & MAX_ID, key))` and then
`prop_assert_eq!(deobfuscate(obfuscate(id, key), key), id & MAX_ID)`.
`id & MAX_ID` is computed with the crate constant `permute::MAX_ID`. -/
def out_of_domain_input_is_reduced_not_rejected_spec (key id : Std.U64) : Prop :=
  (do
    let max_id ← permute.MAX_ID
    let lhs ← permute.obfuscate id key
    let rhs ← permute.obfuscate (id &&& max_id) key
    let code ← permute.obfuscate id key
    let back ← permute.deobfuscate code key
    ok (lhs, rhs, back, id &&& max_id)) ⦃ (lhs, rhs, back, masked) =>
      lhs = rhs ∧ back = masked ⦄

axiom out_of_domain_input_is_reduced_not_rejected (key id : Std.U64) :
    out_of_domain_input_is_reduced_not_rejected_spec key id

axiom output_never_leaves_the_domain (key id : Std.U64) :
    output_never_leaves_the_domain_spec key id

axiom round_trip_over_the_whole_domain (key id : Std.U64)
    (h_id : id.val ≤ 2^40 - 1) :
    round_trip_over_the_whole_domain_spec key id

end Benchmark.Cases.Arxid.Permute.Oracle
