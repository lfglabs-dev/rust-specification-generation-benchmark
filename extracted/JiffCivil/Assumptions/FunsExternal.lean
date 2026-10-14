-- [jiff_core]: external functions.
-- Seeded by hax from Extraction/FunsExternal_Template.lean: fill the holes.
-- hax never modifies this file; after re-extraction, compare it against the
-- regenerated template to see what changed.
import Aeneas
import CoreModels
import JiffCivil.Extraction.Types
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
open jiff_core

/-- [jiff_core::bounds::{jiff_core::bounds::Hour}::checkc]:
    Source: 'crates/jiff-core/src/bounds.rs', lines 86:16-93:17
    Visibility: public -/
axiom bounds.Hour.checkc
  : Std.I64 → RustM (core.result.Result Std.I8 bounds.BoundsError)

/-- [jiff_core::bounds::{jiff_core::bounds::Minute}::checkc]:
    Source: 'crates/jiff-core/src/bounds.rs', lines 86:16-93:17
    Visibility: public -/
axiom bounds.Minute.checkc
  : Std.I64 → RustM (core.result.Result Std.I8 bounds.BoundsError)

/-- [jiff_core::bounds::{jiff_core::bounds::Second}::checkc]:
    Source: 'crates/jiff-core/src/bounds.rs', lines 86:16-93:17
    Visibility: public -/
axiom bounds.Second.checkc
  : Std.I64 → RustM (core.result.Result Std.I8 bounds.BoundsError)

/-- [jiff_core::bounds::{jiff_core::bounds::SubsecNanosecond}::checkc]:
    Source: 'crates/jiff-core/src/bounds.rs', lines 86:16-93:17
    Visibility: public -/
axiom bounds.SubsecNanosecond.checkc
  : Std.I64 → RustM (core.result.Result Std.I32 bounds.BoundsError)

/-- [jiff_core::bounds::{jiff_core::bounds::Millisecond}::checkc]:
    Source: 'crates/jiff-core/src/bounds.rs', lines 86:16-93:17
    Visibility: public -/
axiom bounds.Millisecond.checkc
  : Std.I64 → RustM (core.result.Result Std.I16 bounds.BoundsError)

/-- [jiff_core::bounds::{jiff_core::bounds::Microsecond}::checkc]:
    Source: 'crates/jiff-core/src/bounds.rs', lines 86:16-93:17
    Visibility: public -/
axiom bounds.Microsecond.checkc
  : Std.I64 → RustM (core.result.Result Std.I16 bounds.BoundsError)

/-- [jiff_core::bounds::{jiff_core::bounds::Nanosecond}::checkc]:
    Source: 'crates/jiff-core/src/bounds.rs', lines 86:16-93:17
    Visibility: public -/
axiom bounds.Nanosecond.checkc
  : Std.I64 → RustM (core.result.Result Std.I16 bounds.BoundsError)

/-- [jiff_core::bounds::{jiff_core::bounds::CivilDaySecond}::checkc]:
    Source: 'crates/jiff-core/src/bounds.rs', lines 86:16-93:17
    Visibility: public -/
axiom bounds.CivilDaySecond.checkc
  : Std.I64 → RustM (core.result.Result Std.I32 bounds.BoundsError)

/-- [jiff_core::bounds::{jiff_core::bounds::CivilDayNanosecond}::checkc]:
    Source: 'crates/jiff-core/src/bounds.rs', lines 86:16-93:17
    Visibility: public -/
axiom bounds.CivilDayNanosecond.checkc
  : Std.I64 → RustM (core.result.Result Std.I64 bounds.BoundsError)

/-- [jiff_core::bounds::{jiff_core::bounds::Year}::checkc]:
    Source: 'crates/jiff-core/src/bounds.rs', lines 86:16-93:17
    Visibility: public -/
axiom bounds.Year.checkc
  : Std.I64 → RustM (core.result.Result Std.I16 bounds.BoundsError)

/-- [jiff_core::bounds::{jiff_core::bounds::Month}::checkc]:
    Source: 'crates/jiff-core/src/bounds.rs', lines 86:16-93:17
    Visibility: public -/
axiom bounds.Month.checkc
  : Std.I64 → RustM (core.result.Result Std.I8 bounds.BoundsError)

/-- [jiff_core::civil::time::{jiff_core::civil::time::TimeSecond}::overflowing_add]:
    Source: 'crates/jiff-core/src/civil/time.rs', lines 346:4-356:5
    Visibility: public -/
axiom civil.time.TimeSecond.overflowing_add
  :
  civil.time.TimeSecond → Std.I32 → RustM (core.result.Result
    (civil.time.TimeSecond × Std.I32) bounds.RangeError)

/-- [jiff_core::civil::time::{jiff_core::civil::time::TimeNanosecond}::overflowing_add]:
    Source: 'crates/jiff-core/src/civil/time.rs', lines 420:4-430:5
    Visibility: public -/
axiom civil.time.TimeNanosecond.overflowing_add
  :
  civil.time.TimeNanosecond → Std.I64 → RustM (core.result.Result
    (civil.time.TimeNanosecond × Std.I64) bounds.RangeError)

