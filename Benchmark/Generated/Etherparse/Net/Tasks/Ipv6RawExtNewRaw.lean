import Benchmark.Cases.Etherparse.Net.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Net

/-- `Ipv6RawExtHeader::new_raw` round-trips `payload()`, rejects prefixes shorter
than 6 bytes, rejects a 2047-byte payload, and rejects the unaligned lengths
the test builds by extending the serialized header. -/
def ipv6_raw_ext_new_raw_spec (header : net.ipv6_raw_ext_header.Ipv6RawExtHeader) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Etherparse.Net
