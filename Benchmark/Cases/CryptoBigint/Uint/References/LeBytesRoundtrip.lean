import Benchmark.Cases.CryptoBigint.Uint.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open crypto_bigint

namespace Benchmark.Cases.CryptoBigint.Uint

/-- Decoding the 32-byte little-endian encoding of the value of any `U256` `a` with `U256::from_le_slice` never panics and returns `a` itself. -/
def le_bytes_roundtrip_spec (a : uint.Uint 4#usize) : Prop :=
  (uint.encoding.Uint.from_le_slice 4#usize (Array.to_slice (leBytes32 (uintVal a))))
    ⦃ r => r = a ⦄

end Benchmark.Cases.CryptoBigint.Uint
