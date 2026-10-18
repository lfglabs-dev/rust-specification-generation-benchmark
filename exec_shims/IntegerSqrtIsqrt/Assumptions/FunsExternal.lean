-- [integer_sqrt]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import IntegerSqrtIsqrt.Extraction.Types
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
set_option maxRecDepth 100000
open integer_sqrt


/-! rsgb exec shim: `core::num::<ty>::wrapping_shr` is modelled by Aeneas as
`Aeneas.Std.core.num.<Ty>.wrapping_shr` (pure), which the generated header hides
(`hiding namespace core`). The extraction calls it monadically: lift the Aeneas model. -/
namespace CoreModels.core.num
abbrev U8.wrapping_shr (x : Std.U8) (s : Std.U32) : RustM Std.U8 := RustM.ok (Aeneas.Std.core.num.U8.wrapping_shr x s)
abbrev U16.wrapping_shr (x : Std.U16) (s : Std.U32) : RustM Std.U16 := RustM.ok (Aeneas.Std.core.num.U16.wrapping_shr x s)
abbrev U32.wrapping_shr (x : Std.U32) (s : Std.U32) : RustM Std.U32 := RustM.ok (Aeneas.Std.core.num.U32.wrapping_shr x s)
abbrev U64.wrapping_shr (x : Std.U64) (s : Std.U32) : RustM Std.U64 := RustM.ok (Aeneas.Std.core.num.U64.wrapping_shr x s)
abbrev U128.wrapping_shr (x : Std.U128) (s : Std.U32) : RustM Std.U128 := RustM.ok (Aeneas.Std.core.num.U128.wrapping_shr x s)
abbrev Usize.wrapping_shr (x : Std.Usize) (s : Std.U32) : RustM Std.Usize := RustM.ok (Aeneas.Std.core.num.Usize.wrapping_shr x s)
abbrev I8.wrapping_shr (x : Std.I8) (s : Std.U32) : RustM Std.I8 := RustM.ok (Aeneas.Std.core.num.I8.wrapping_shr x s)
abbrev I16.wrapping_shr (x : Std.I16) (s : Std.U32) : RustM Std.I16 := RustM.ok (Aeneas.Std.core.num.I16.wrapping_shr x s)
abbrev I32.wrapping_shr (x : Std.I32) (s : Std.U32) : RustM Std.I32 := RustM.ok (Aeneas.Std.core.num.I32.wrapping_shr x s)
abbrev I64.wrapping_shr (x : Std.I64) (s : Std.U32) : RustM Std.I64 := RustM.ok (Aeneas.Std.core.num.I64.wrapping_shr x s)
abbrev I128.wrapping_shr (x : Std.I128) (s : Std.U32) : RustM Std.I128 := RustM.ok (Aeneas.Std.core.num.I128.wrapping_shr x s)
abbrev Isize.wrapping_shr (x : Std.Isize) (s : Std.U32) : RustM Std.Isize := RustM.ok (Aeneas.Std.core.num.Isize.wrapping_shr x s)
end CoreModels.core.num
