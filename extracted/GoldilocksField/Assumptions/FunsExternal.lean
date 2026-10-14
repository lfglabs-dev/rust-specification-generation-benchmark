-- [goldilocks_ntt]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import GoldilocksField.Extraction.Types
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
open goldilocks_ntt

/-- [goldilocks_ntt::utils::branch_hint]:
    Source: 'ntt/src/utils.rs', lines 9:0-13:1
    Visibility: public -/
axiom utils.branch_hint : RustM Unit

/-- [goldilocks_ntt::field::algo::generic::inv_ebgcd]:
    Source: 'ntt/src/field/algo/generic.rs', lines 220:0-271:1 -/
axiom field.algo.generic.inv_ebgcd : Std.U64 → RustM Std.U64

