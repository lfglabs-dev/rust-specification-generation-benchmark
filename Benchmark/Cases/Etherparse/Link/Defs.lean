import EtherparseLink.Extraction

/-!
# etherparse (link layer) — specifications

Implementation: `extracted/EtherparseLink` (verbatim `cargo hax extract
etherparse-link` output for JulianSchmid/etherparse@70f72bee, crate
`etherparse` 0.21.0, `--no-default-features`).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Arithmetic in
the extracted code follows Rust debug-build semantics (overflow and
`debug_assert!` failures panic), which is the configuration `cargo test` runs
the original property tests under.

Conventions used below:
* newtype wrappers (`EtherType(u16)`, `LinuxSllPacketType(u16)`,
  `ArpHardwareId(u16)`, `MacsecShortLen(u8)`, ...) are extracted as reducible
  aliases of the wrapped scalar, so `x.0` / `x.value()` is the scalar itself;
* `&mut self` methods return the updated value (`set_payload_len`);
* `x.clone()` of the derived `Clone` impls is `x` itself;
* `.unwrap()` / `.unwrap_err()` succeed iff the result is `Ok` / `Err`, so the
  postconditions require the corresponding constructor.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Etherparse.Link

open etherparse

end Benchmark.Cases.Etherparse.Link
