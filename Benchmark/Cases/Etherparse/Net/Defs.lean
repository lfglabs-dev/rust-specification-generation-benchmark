import EtherparseNet.Extraction

/-!
# etherparse (network layer) — specifications

Implementation: `extracted/EtherparseNet` (verbatim `cargo hax extract
etherparse-net` output for JulianSchmid/etherparse@70f72bee, crate
`etherparse` 0.21.0, `--no-default-features`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow panics), which
is the configuration `cargo test` runs the original property tests under.

`IpDscp`, `IpNumber` and `Ipv6FlowLabel` are extracted as reducible aliases of
the wrapped scalar. `Ipv4Options.len()` is the extracted `impl.len` (a `u8` to
`usize` cast of the length field).
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Etherparse.Net

open etherparse

end Benchmark.Cases.Etherparse.Net
