import EtherparseTransport.Extraction

/-!
# etherparse (transport layer) — specifications

Implementation: `extracted/EtherparseTransport` (verbatim `cargo hax extract
etherparse-transport` output for JulianSchmid/etherparse@70f72bee, crate
`etherparse` 0.21.0, `--no-default-features`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Bitwise
operators are the extracted debug-build `u8` operations (a shift amount
`≥ 8` panics).

`MaxResponseCode` is a reducible alias of `u8`. `GroupAddress::new([0, 0, 0, 0])`
is the public-field constructor `{ octets }`; the test's array literal is
`Array.repeat 4 0`.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Etherparse.Transport

open etherparse

end Benchmark.Cases.Etherparse.Transport
