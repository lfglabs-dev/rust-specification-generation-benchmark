-- [bloom2]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import Bloom2VecBitmap.Extraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open bloom2

/-- [bloom2::bitmap::vec::{impl bloom2::bloom::Bitmap for bloom2::bitmap::vec::VecBitmap}::or]:
    Source: 'src/bitmap/vec.rs', lines 45:4-61:5
    Visibility: public -/
axiom bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.or
  :
  bitmap.vec.VecBitmap → bitmap.vec.VecBitmap → RustM bitmap.vec.VecBitmap

/-- [bloom2::bitmap::vec::{impl bloom2::bloom::Bitmap for bloom2::bitmap::vec::VecBitmap}::byte_size]:
    Source: 'src/bitmap/vec.rs', lines 41:4-43:5
    Visibility: public -/
axiom bitmap.vec.VecBitmap.Insts.Bloom2BloomBitmap.byte_size
  : bitmap.vec.VecBitmap → RustM Std.Usize

