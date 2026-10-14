import ByteorderEndian.Extraction

/-!
# byteorder — specifications

Implementation: `extracted/ByteorderEndian` (verbatim `cargo hax extract
byteorder-endian` output for BurntSushi/byteorder@5a82625f): the methods
`read_u16/u32/u64/u128` and `write_u16/u32/u64/u128` of
`impl ByteOrder for BigEndian` and `impl ByteOrder for LittleEndian`.

The property tests are the `qc_byte_order!` round trips of `src/lib.rs`
(`mod test`, macro template at lines 2349-2393). Each spec executes the test
body in the extracted semantics:

* `let mut buf = [0; 16]` is `Array.repeat 16#usize 0#u8`;
* `&mut buf[a..]` / `&mut buf[..b]` is CoreModels' `IndexMut` for arrays with a
  `RangeFrom`/`RangeTo` index (it returns the sub-slice and the write-back
  function that puts the updated sub-slice back into the array);
* `&buf[a..]` / `&buf[..b]` is CoreModels' `Index` for arrays;
* `BigEndian::write_uN(..)` / `read_uN(..)` are the extracted impl methods;
* `size_of::<uN>()` is the compile-time constant `N/8` (written as a numeral),
  and the big-endian offset `16 - size_of::<uN>()` is computed with the Rust
  `usize` subtraction of the extracted semantics;
* `n.clone()` is `n` (`Copy` integers; for `Wi128<u128>` the test's inherent
  `clone` returns the wrapped `u128`), and `n == r` is equality of the values
  (for `Wi128<u128>`, `PartialEq<u128>` compares the wrapped value).

Notation: `e ⦃ r => P r ⦄` (Aeneas `WP.spec`) holds iff the Rust computation `e`
terminates without panicking, returning `ok r`, and `P r` holds. Any panic
(out-of-range slicing, the `unwrap` of `<[u8; N]>::try_from`, a length
mismatch in `copy_from_slice`) makes the spec false, exactly as it would make
the quickcheck property fail.
-/

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM

namespace Benchmark.Cases.Byteorder.Endian

open byteorder

end Benchmark.Cases.Byteorder.Endian
