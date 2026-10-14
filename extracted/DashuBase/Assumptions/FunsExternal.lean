-- [dashu_base]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import DashuBase.Extraction.Types
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
open dashu_base

/-- [dashu_base::bit::{impl dashu_base::bit::PowerOfTwo for u8}::next_power_of_two]:
    Source: 'base/src/bit.rs', lines 93:12-95:13
    Visibility: public -/
axiom U8.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two
  : Std.U8 → RustM Std.U8

/-- [dashu_base::bit::{impl dashu_base::bit::PowerOfTwo for u16}::next_power_of_two]:
    Source: 'base/src/bit.rs', lines 93:12-95:13
    Visibility: public -/
axiom U16.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two
  : Std.U16 → RustM Std.U16

/-- [dashu_base::bit::{impl dashu_base::bit::PowerOfTwo for u32}::next_power_of_two]:
    Source: 'base/src/bit.rs', lines 93:12-95:13
    Visibility: public -/
axiom U32.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two
  : Std.U32 → RustM Std.U32

/-- [dashu_base::bit::{impl dashu_base::bit::PowerOfTwo for u64}::next_power_of_two]:
    Source: 'base/src/bit.rs', lines 93:12-95:13
    Visibility: public -/
axiom U64.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two
  : Std.U64 → RustM Std.U64

/-- [dashu_base::bit::{impl dashu_base::bit::PowerOfTwo for u128}::next_power_of_two]:
    Source: 'base/src/bit.rs', lines 93:12-95:13
    Visibility: public -/
axiom U128.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two
  : Std.U128 → RustM Std.U128

/-- [dashu_base::bit::{impl dashu_base::bit::PowerOfTwo for usize}::next_power_of_two]:
    Source: 'base/src/bit.rs', lines 93:12-95:13
    Visibility: public -/
axiom Usize.Insts.Dashu_baseBitPowerOfTwo.next_power_of_two
  : Std.Usize → RustM Std.Usize

