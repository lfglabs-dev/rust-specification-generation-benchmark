import Benchmark.Exec.Runtime
import EtherparseLink.Extraction

/-! Grader-side instances for target `etherparse/link`: decidable equality and
`Repr` for the crate's result types (gold spec, diff probes) and `Arbitrary`
for the header structs (so that the upstream oracles, whose inputs are headers,
can be executed by `baseline`). -/

open CoreModels Aeneas Aeneas.Std


deriving instance DecidableEq, Repr for CoreModels.core.result.Result
deriving instance DecidableEq, Repr for etherparse.err.layer.Layer
deriving instance DecidableEq, Repr for etherparse.err.slice_write_space_error.SliceWriteSpaceError
deriving instance DecidableEq, Repr for etherparse.err.linux_sll.header_error.HeaderError
deriving instance DecidableEq, Repr for etherparse.link.linux_sll_protocol_type.LinuxSllProtocolType
deriving instance DecidableEq, Repr for etherparse.link.linux_sll_header.LinuxSllHeader
deriving instance DecidableEq, Repr for etherparse.link.ethernet2_header.Ethernet2Header
deriving instance Plausible.Arbitrary for etherparse.link.linux_sll_protocol_type.LinuxSllProtocolType
deriving instance Plausible.Arbitrary for etherparse.link.linux_sll_header.LinuxSllHeader
deriving instance Plausible.Arbitrary for etherparse.link.ethernet2_header.Ethernet2Header
