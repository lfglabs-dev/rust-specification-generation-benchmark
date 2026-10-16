import Benchmark.Exec.Runtime
import EtherparseTransport.Extraction

/-! Grader-side instances for target `etherparse/transport`: decidable equality
and `Repr` for the crate's result types (gold spec and diff probes). -/

open CoreModels Aeneas Aeneas.Std


deriving instance DecidableEq, Repr for CoreModels.core.result.Result
deriving instance DecidableEq, Repr for CoreModels.core.cmp.Ordering
deriving instance DecidableEq, Repr for etherparse.err.value_type.ValueType
deriving instance DecidableEq, Repr for etherparse.err.value_too_big_error.ValueTooBigError
deriving instance DecidableEq, Repr for etherparse.transport.igmp.group_address.GroupAddress
deriving instance DecidableEq, Repr for
  etherparse.transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader
deriving instance DecidableEq, Repr for etherparse.transport.udp_header.UdpHeader
