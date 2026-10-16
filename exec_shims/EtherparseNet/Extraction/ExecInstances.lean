import EtherparseNet.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for etherparse.err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError
deriving instance Repr for etherparse.err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError
deriving instance Plausible.Arbitrary for etherparse.err.ipv6_exts.ext_payload_len_error.ExtPayloadLenError
deriving instance DecidableEq for etherparse.err.layer.Layer
deriving instance Repr for etherparse.err.layer.Layer
deriving instance Plausible.Arbitrary for etherparse.err.layer.Layer
deriving instance DecidableEq for etherparse.len_source.LenSource
deriving instance Repr for etherparse.len_source.LenSource
deriving instance Plausible.Arbitrary for etherparse.len_source.LenSource
deriving instance DecidableEq for etherparse.err.len_error.LenError
deriving instance Repr for etherparse.err.len_error.LenError
deriving instance Plausible.Arbitrary for etherparse.err.len_error.LenError
deriving instance DecidableEq for etherparse.err.value_type.ValueType
deriving instance Repr for etherparse.err.value_type.ValueType
deriving instance Plausible.Arbitrary for etherparse.err.value_type.ValueType
deriving instance DecidableEq for etherparse.err.value_too_big_error.ValueTooBigError
deriving instance Repr for etherparse.err.value_too_big_error.ValueTooBigError
deriving instance Plausible.Arbitrary for etherparse.err.value_too_big_error.ValueTooBigError
deriving instance DecidableEq for etherparse.net.ip_ecn.IpEcn
deriving instance Repr for etherparse.net.ip_ecn.IpEcn
deriving instance Plausible.Arbitrary for etherparse.net.ip_ecn.IpEcn
deriving instance DecidableEq for etherparse.net.ipv4_options.Ipv4Options
deriving instance Repr for etherparse.net.ipv4_options.Ipv4Options
deriving instance Plausible.Arbitrary for etherparse.net.ipv4_options.Ipv4Options
deriving instance DecidableEq for etherparse.net.ipv4_header.Ipv4Header
deriving instance Repr for etherparse.net.ipv4_header.Ipv4Header
deriving instance Plausible.Arbitrary for etherparse.net.ipv4_header.Ipv4Header
deriving instance DecidableEq for etherparse.net.ipv6_header.Ipv6Header
deriving instance Repr for etherparse.net.ipv6_header.Ipv6Header
deriving instance Plausible.Arbitrary for etherparse.net.ipv6_header.Ipv6Header
deriving instance DecidableEq for etherparse.net.ipv6_raw_ext_header.Ipv6RawExtHeader
deriving instance Repr for etherparse.net.ipv6_raw_ext_header.Ipv6RawExtHeader
deriving instance Plausible.Arbitrary for etherparse.net.ipv6_raw_ext_header.Ipv6RawExtHeader
