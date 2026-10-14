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
  (do
    let before ← net.ipv6_header.Ipv6Header.dscp header
    let shifted ← header.traffic_class >>> 2#i32
    let decoded ← net.ip_dscp.IpDscp.try_new shifted
    let header1 ← net.ipv6_header.Ipv6Header.set_dscp header dscp
    let shifted1 ← header1.traffic_class >>> 2#i32
    let decoded1 ← net.ip_dscp.IpDscp.try_new shifted1
    let after ← net.ipv6_header.Ipv6Header.dscp header1
    ok (before, decoded, decoded1, after))
    ⦃ t =>
      (∃ v, t.2.1 = core.result.Result.Ok v ∧ t.1 = v) ∧
      (∃ v, t.2.2.1 = core.result.Result.Ok v ∧ v = dscp) ∧
      t.2.2.2 = dscp ⦄

end Benchmark.Cases.Etherparse.Net
