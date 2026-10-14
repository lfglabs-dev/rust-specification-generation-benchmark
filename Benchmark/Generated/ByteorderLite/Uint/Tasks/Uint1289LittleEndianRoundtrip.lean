import Benchmark.Cases.ByteorderLite.Uint.Defs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open byteorder_lite

namespace Benchmark.Cases.ByteorderLite.Uint

/-- Writing any `n < 2^72` with `LittleEndian::write_uint128(&mut buf, n, 9)` into a zeroed 16-byte buffer and reading the first 9 bytes back with `LittleEndian::read_uint128(&buf[..9], 9)` never panics and returns the same value. -/
def uint128_9_little_endian_roundtrip_spec (n : Std.U128) : Prop :=
  -- Replace this placeholder with the formal specification.
  True

end Benchmark.Cases.ByteorderLite.Uint
