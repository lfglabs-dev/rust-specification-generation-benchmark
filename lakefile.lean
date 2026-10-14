import Lake
open Lake DSL

package RustVerificationBenchmark where
  version := v!"0.1.0"

-- Pinned to the defaults of cargo-hax v0.4.1 (see toolchain.json).
require aeneas from git
  "https://github.com/cryspen/aeneas" @ "build-183e4f0" / "backends/lean"

require hax from git
  "https://github.com/cryspen/hax-lean" @ "v0.3.27"

/-- Verbatim `cargo hax extract` output, one Lean package per case scenario. -/
lean_lib Extracted where
  srcDir := "extracted"
  globs := #[
    .submodules `ArxidPermute,
    .submodules `Bloom2VecBitmap,
    .submodules `BlueScrunchBinarySearch,
    .submodules `ByteorderEndian,
    .submodules `ByteorderLiteUint,
    .submodules `Crc32fastBaseline,
    .submodules `CryptoBigintUint,
    .submodules `DashuBase,
    .submodules `DltParseStorageHeader,
    .submodules `EtherparseLink,
    .submodules `EtherparseNet,
    .submodules `EtherparseTransport,
    .submodules `FastdivideDivider,
    .submodules `GoldilocksField,
    .submodules `IndexedBitvecWord,
    .submodules `JiffCivil,
    .submodules `LilliputIntValue,
    .submodules `MemchrTwoway,
    .submodules `NtTimeFileTime,
    .submodules `OpenpqlPreludeCard,
    .submodules `OpenpqlPreludeUtil,
    .submodules `OrderStatQuickselect,
    .submodules `PartitionSlicePartition,
    .submodules `Plonky3Monty31Utils,
    .submodules `Plonky3Util,
    .submodules `QuantilesGreenwaldKhanna,
    .submodules `RevBitsU32,
    .submodules `RuintGcdMatrix,
    .submodules `RuintUintAdd,
    .submodules `RustCrdtDot,
    .submodules `SdsetDuoUnion,
    .submodules `SigmaSerZigzag,
    .submodules `StaticFilezSlice,
    .submodules `SuccinctBroadword,
    .submodules `TinysetFits64,
    .submodules `UintU64,
    .submodules `UseCombinatoricsCounting,
    .submodules `VaringPackable
  ]

/-- Specifications and reference proofs (`Benchmark/Cases/*/*/Proofs`). The
editable task skeletons under `Benchmark/Generated` are intentionally not part
of the default target (they contain `exact ?_` placeholders). -/
@[default_target]
lean_lib Benchmark where
  globs := #[.one `Benchmark, .submodules `Benchmark.Cases]

lean_exe spec_audit where
  root := `Benchmark.SpecAudit
  supportInterpreter := true
