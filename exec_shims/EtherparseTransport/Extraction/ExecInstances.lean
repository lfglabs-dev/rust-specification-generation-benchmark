import EtherparseTransport.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for etherparse.err.value_type.ValueType
deriving instance Repr for etherparse.err.value_type.ValueType
deriving instance Plausible.Arbitrary for etherparse.err.value_type.ValueType
deriving instance DecidableEq for etherparse.err.value_too_big_error.ValueTooBigError
deriving instance Repr for etherparse.err.value_too_big_error.ValueTooBigError
deriving instance Plausible.Arbitrary for etherparse.err.value_too_big_error.ValueTooBigError
deriving instance DecidableEq for etherparse.transport.igmp.group_address.GroupAddress
deriving instance Repr for etherparse.transport.igmp.group_address.GroupAddress
deriving instance Plausible.Arbitrary for etherparse.transport.igmp.group_address.GroupAddress
deriving instance DecidableEq for etherparse.transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader
deriving instance Repr for etherparse.transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader
deriving instance Plausible.Arbitrary for etherparse.transport.igmp.membership_query_with_sources_header.MembershipQueryWithSourcesHeader
deriving instance DecidableEq for etherparse.transport.udp_header.UdpHeader
deriving instance Repr for etherparse.transport.udp_header.UdpHeader
deriving instance Plausible.Arbitrary for etherparse.transport.udp_header.UdpHeader
