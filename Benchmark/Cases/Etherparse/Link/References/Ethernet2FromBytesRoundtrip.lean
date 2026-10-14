import Benchmark.Cases.Etherparse.Link.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Link

/-- Serialising an Ethernet II header to its 14 wire bytes and parsing them back
never panics and yields the original header. -/
def ethernet2_from_bytes_roundtrip_spec (input : link.ethernet2_header.Ethernet2Header) : Prop :=
  (do
    let bytes ← link.ethernet2_header.Ethernet2Header.to_bytes input
    link.ethernet2_header.Ethernet2Header.from_bytes bytes)
    ⦃ r => r = input ⦄

end Benchmark.Cases.Etherparse.Link
