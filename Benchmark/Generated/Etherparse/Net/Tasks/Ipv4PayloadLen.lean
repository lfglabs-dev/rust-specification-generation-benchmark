import Benchmark.Cases.Etherparse.Net.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Net

/-- `Ipv4Header::payload_len` equals `total_len - 20 - options.len() as u16` when
the total length covers the header, and returns `LenError` for every smaller
`total_len`. -/
def ipv4_payload_len_spec (header : net.ipv4_header.Ipv4Header) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Etherparse.Net
