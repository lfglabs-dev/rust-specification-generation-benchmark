import Benchmark.Cases.Etherparse.Link.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Link

/-- Serialising a Linux cooked-capture (SLL) header with `to_bytes` and parsing the
16 bytes back with `from_bytes` never panics and returns `Ok` of the original
header, for every header built like the test generator `linux_sll_any()`. -/
def linux_sll_from_bytes_roundtrip_spec (input : link.linux_sll_header.LinuxSllHeader) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Etherparse.Link
