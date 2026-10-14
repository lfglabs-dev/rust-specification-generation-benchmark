import Benchmark.Cases.Uint.U64.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open ethereum_types
open Benchmark.Cases.Uint.U64

namespace Benchmark.Cases.Uint.U64.Oracle

/-- quickcheck `laws::u64::associative_add` (uint/tests/uint_tests.rs:1204-1214, `uint_laws!(u64, U64)`):

```rust
fn associative_add(x: U64, y: U64, z: U64) -> TestResult {
    if x.overflowing_add(y).1 || y.overflowing_add(z).1 || (x + y).overflowing_add(z).1 {
        return TestResult::discard();
    }
    TestResult::from_bool((x + y) + z == x + (y + z))
}
``` -/
def associative_add_spec (x y z : uint.U64) : Prop :=
  (do
    let xy ← add x y
    let lhs ← add xy z
    let yz ← add y z
    let rhs ← add x yz
    uint.U64.Insts.CoreCmpPartialEqU64.eq lhs rhs) ⦃ b => b = true ⦄

/-- quickcheck `laws::u64::commutative_add` (uint/tests/uint_tests.rs:1228-1238):

```rust
fn commutative_add(x: U64, y: U64) -> TestResult {
    if x.overflowing_add(y).1 { return TestResult::discard(); }
    TestResult::from_bool(x + y == y + x)
}
``` -/
def commutative_add_spec (x y : uint.U64) : Prop :=
  (do
    let lhs ← add x y
    let rhs ← add y x
    uint.U64.Insts.CoreCmpPartialEqU64.eq lhs rhs) ⦃ b => b = true ⦄

axiom associative_add (x y z : uint.U64)
    (h_assume_xy : uint.U64.overflowing_add x y ⦃ r => r.2 = false ⦄)
    (h_assume_yz : uint.U64.overflowing_add y z ⦃ r => r.2 = false ⦄)
    (h_assume_xyz : (do
      let xy ← add x y
      uint.U64.overflowing_add xy z) ⦃ r => r.2 = false ⦄) :
    associative_add_spec x y z

end Benchmark.Cases.Uint.U64.Oracle
