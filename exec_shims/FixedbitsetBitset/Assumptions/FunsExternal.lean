-- [fixedbitset]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import FixedbitsetBitset.Extraction.Types
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
open fixedbitset



/-! Executable-copy shim (grader side): models of Rust core items that CoreModels
lacks, used only to build `assert!` panic messages (`fmt::rt::Argument::new_display`)
and `u32::max_value()`. No fixedbitset code here. -/
namespace CoreModels.core

def fmt.rt.Argument.new_display {T : Type} (_inst : fmt.Display T) (_x : T) :
    RustM fmt.rt.Argument :=
  ok ⟨fmt.rt.ArgumentType.Placeholder ⟨⟩⟩

def num.U32.max_value : RustM Std.U32 := ok ⟨BitVec.allOnes 32⟩

/-- `impl BitAnd<u32> for &u32` -/
def Shared0U32.Insts.CoreOpsBitBitAndU32U32.bitand (a b : Std.U32) : RustM Std.U32 :=
  ok (a &&& b)

end CoreModels.core
