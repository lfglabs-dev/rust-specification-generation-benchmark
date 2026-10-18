-- [slab]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import SlabSlab.Extraction.Types
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
open slab


/-! Executable-copy shim (grader side): model of the Rust core item
`impl<T> From<T> for Option<T>` (`Some`), which CoreModels lacks.
Used by `Slab::try_remove` (`val.into()`). No slab code here. -/
namespace CoreModels.core.option

def Option.Insts.CoreConvertFrom.from {T : Type} (x : T) : RustM (Option T) := do
  ok (Option.Some x)

@[reducible]
def Option.Insts.CoreConvertFrom (T : Type) : convert.From (Option T) T := {
  «from» := Option.Insts.CoreConvertFrom.from
}

end CoreModels.core.option
