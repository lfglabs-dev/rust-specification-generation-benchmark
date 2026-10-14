import ByteorderLiteUint.Extraction

/-!
# byteorder-lite — specifications (variable-width unsigned integers)

Implementation: `extracted/ByteorderLiteUint` (verbatim `cargo hax extract
byteorder-lite-uint` output for image-rs/byteorder-lite@7d44da06): the methods
`read_uint`, `write_uint`, `read_uint128`, `write_uint128` of
`impl ByteOrder for BigEndian` and `impl ByteOrder for LittleEndian`, and the
private helpers `pack_size` / `pack_size128` they call.

The property tests are the first arm of the `qc_byte_order!` macro in
`src/lib.rs` (`mod test`, macro template at lines 2384-2428; the
`big_endian`/`little_endian` bodies are at lines 2396-2403 / 2406-2413),
instantiated as `prop_uint_N` (`u64`, `read_uint`/`write_uint`, N = 1..8) and
`prop_uint128_N` (`Wi128<u128>`, `read_uint128`/`write_uint128`, N = 1..16):

```rust
fn prop(n: $ty_int) -> bool {
    let mut buf = [0; 16];
    BigEndian::$write(&mut buf, n.clone(), $bytes);      // resp. LittleEndian
    n == BigEndian::$read(&buf[..$bytes], $bytes)
}
qc_sized(prop as fn($ty_int) -> bool, $max);
```

Each spec executes this body in the extracted semantics:

* `let mut buf = [0; 16]` is `Array.repeat 16#usize 0#u8`;
* `&mut buf` passed where `&mut [u8]` is expected is the array-to-slice
  unsizing coercion, which Aeneas translates as
  `let (s, back) ← lift (Array.to_slice_mut buf)`; the updated array after the
  call is `back s'`;
* `&buf[..N]` is CoreModels' `Index` for arrays with a `RangeTo` index;
* `BigEndian::write_uint(..)` / `read_uint(..)` (and the `128`/`LittleEndian`
  variants) are the extracted impl methods, called with the literal byte count
  `N` of the macro instance;
* `n.clone()` is `n` (`u64` is `Copy`; for `Wi128<u128>` the test's inherent
  `clone` returns the wrapped `u128`), and `n == r` is equality of the values
  (for `Wi128<u128>`, `PartialEq<u128>` compares the wrapped value).

Generated inputs (the theorems' hypotheses): `write_uint(buf, n, N)` asserts
`pack_size(n) <= N`, i.e. `n < 2^(8N)`, so the round trip is false without a
bound; the tests bound `n` through their generator:

* `prop_uint_N`: quickcheck 0.9 `Arbitrary for u64` samples
  `gen_range(0, size)` with `size = calc_max!(u64::MAX, N) = (2^64 - 2) >> (8 * (8 - N))`,
  i.e. `n ∈ [0, 2^(8N) - 2]` for `N < 8` and `n ∈ [0, 2^64 - 3]` for `N = 8`;
* `prop_uint128_N`: `Arbitrary for Wi128<u128>` draws a uniform `u128`
  `output` and returns `output & (max - 1)` with
  `max = calc_max!(u128::MAX, N, 16) = (2^128 - 2) >> (8 * (16 - N))`,
  i.e. the value is masked to `n < 2^(8N)` (and, as an artefact of the
  `max - 1`, one low bit is always cleared).

The theorems take the exact no-panic domain of the writer, `n < 2^(8N)`, as
hypothesis (no hypothesis for the full widths `N = 8` / `N = 16`): a superset
of every sampled value, so each theorem implies the property on the test's
domain.

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Any panic (the
`assert!`s of `write_uint`/`read_uint`, out-of-range slicing, a length mismatch
in `copy_from_slice`, an arithmetic overflow) makes the spec false, exactly as
it would make the quickcheck property fail.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.ByteorderLite.Uint

open byteorder_lite

end Benchmark.Cases.ByteorderLite.Uint
