import Benchmark.Cases.Etherparse.Net.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Net

/-- Before `set_dscp`, `dscp()` agrees with `IpDscp::try_new(traffic_class >> 2)`;
afterwards both equal the value that was written. -/
def ipv6_set_dscp_spec (header : net.ipv6_header.Ipv6Header)
    (dscp : net.ip_dscp.IpDscp) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.Etherparse.Net
