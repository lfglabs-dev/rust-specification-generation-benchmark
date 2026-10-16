import EtherparseLink.Extraction.Types
import Benchmark.Exec.Runtime

/-! Grader-side instances for the crate types (executable copy only). -/

open CoreModels Aeneas Aeneas.Std Plausible RSGB.Exec

deriving instance DecidableEq for etherparse.err.layer.Layer
deriving instance Repr for etherparse.err.layer.Layer
deriving instance Plausible.Arbitrary for etherparse.err.layer.Layer
deriving instance DecidableEq for etherparse.err.linux_sll.header_error.HeaderError
deriving instance Repr for etherparse.err.linux_sll.header_error.HeaderError
deriving instance Plausible.Arbitrary for etherparse.err.linux_sll.header_error.HeaderError
deriving instance DecidableEq for etherparse.err.slice_write_space_error.SliceWriteSpaceError
deriving instance Repr for etherparse.err.slice_write_space_error.SliceWriteSpaceError
deriving instance Plausible.Arbitrary for etherparse.err.slice_write_space_error.SliceWriteSpaceError
deriving instance DecidableEq for etherparse.err.value_type.ValueType
deriving instance Repr for etherparse.err.value_type.ValueType
deriving instance Plausible.Arbitrary for etherparse.err.value_type.ValueType
deriving instance DecidableEq for etherparse.err.value_too_big_error.ValueTooBigError
deriving instance Repr for etherparse.err.value_too_big_error.ValueTooBigError
deriving instance Plausible.Arbitrary for etherparse.err.value_too_big_error.ValueTooBigError
deriving instance DecidableEq for etherparse.link.ethernet2_header.Ethernet2Header
deriving instance Repr for etherparse.link.ethernet2_header.Ethernet2Header
deriving instance Plausible.Arbitrary for etherparse.link.ethernet2_header.Ethernet2Header
deriving instance DecidableEq for etherparse.link.linux_sll_protocol_type.LinuxSllProtocolType
deriving instance Repr for etherparse.link.linux_sll_protocol_type.LinuxSllProtocolType
deriving instance Plausible.Arbitrary for etherparse.link.linux_sll_protocol_type.LinuxSllProtocolType
deriving instance DecidableEq for etherparse.link.linux_sll_header.LinuxSllHeader
deriving instance Repr for etherparse.link.linux_sll_header.LinuxSllHeader
deriving instance Plausible.Arbitrary for etherparse.link.linux_sll_header.LinuxSllHeader
deriving instance DecidableEq for etherparse.link.macsec_ptype.MacsecPType
deriving instance Repr for etherparse.link.macsec_ptype.MacsecPType
deriving instance Plausible.Arbitrary for etherparse.link.macsec_ptype.MacsecPType
deriving instance DecidableEq for etherparse.link.macsec_header.MacsecHeader
deriving instance Repr for etherparse.link.macsec_header.MacsecHeader
deriving instance Plausible.Arbitrary for etherparse.link.macsec_header.MacsecHeader
