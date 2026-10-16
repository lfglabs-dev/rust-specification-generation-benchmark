"""Independent verifier: pristine repo copy + one submitted editable specification file.

Steps (all must pass):
  1. static policy (imports, forbidden tokens, textual specification signature);
  2. copy the pristine benchmark (lakefile, extracted implementation, Defs, Specs)
     into a fresh directory and overlay only the submitted editable file;
  3. `lake build <task module>` (full elaboration + kernel checking);
  4. a check module, elaborated in a context that never saw the submission's
     source, checks `noncomputable def rsgb_check : <canonical type> := @<spec_name>`,
     so the submitted specification must have (definitionally) the canonical type;
  5. `#print axioms rsgb_check` must be a subset of the trusted Lean axioms;
  6. `spec_audit` lowers both the hidden ground-truth `OracleSpec` and the
     submitted `CandidateSpec` from the Lean 4 kernel environment under the
     domain preconditions `Pre`, and Z3 verifies bidirectional logical
     equivalence (`soundness=unsat`, `completeness=unsat`) as well as
     `nonvacuity=sat` and `nontriviality=sat`.
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

from . import ROOT
from .limits import lake_command, run_limited
from .policy import policy_failure, split_statement
from .tasks import Task, opens_block
from .z3_spec import check_spec_equivalence

TRUSTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
COPY_ROOTS = ["lakefile.lean", "lake-manifest.json", "lean-toolchain", "extracted", "Benchmark"]
CHECK_NS = "Benchmark.VerifierCheck"


@dataclass
class VerifyResult:
    task_id: str
    spec_name: str
    status: str
    detail: str = ""
    axioms: list[str] | None = None
    soundness: str | None = None
    completeness: str | None = None
    nonvacuity: str | None = None
    nontriviality: str | None = None
    counterexample: dict[str, str] | None = None
    submitted_sha256: str | None = None
    duration_seconds: float = 0.0

    @property
    def passed(self) -> bool:
        return self.status == "passed"

    def to_json(self) -> dict:
        return {
            "task_id": self.task_id,
            "pass": self.passed,
            "status": self.status,
            "detail": self.detail,
            "axioms": self.axioms,
            "spec_name": self.spec_name,
            "z3": {
                "soundness": self.soundness,
                "completeness": self.completeness,
                "nonvacuity": self.nonvacuity,
                "nontriviality": self.nontriviality,
                "counterexample": self.counterexample,
            },
            "submitted_sha256": self.submitted_sha256,
            "duration_seconds": self.duration_seconds,
        }


def sha256_text(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


def run(cmd: list[str], cwd: Path, timeout: int) -> tuple[int, str]:
    gated = False
    if cmd and cmd[0] == "lake":
        cmd, gated = lake_command(cmd[1:])
    code, out = run_limited(cmd, cwd, timeout, gated=gated)
    return code, (out + "\ntimeout" if code == 124 else out)


def compact(output: str, limit: int = 6000) -> str:
    lines = [
        l for l in output.splitlines()
        if not l.startswith("trace:") and "LEAN_PATH=" not in l
        and not l.startswith("✔") and not l.startswith("⣿")
    ]
    errs: list[str] = []
    for i, line in enumerate(lines):
        if "error" in line.lower():
            errs.extend(lines[i : i + 12])
    text = "\n".join(errs or lines)
    return text[-limit:]


def link_lake_packages(dst: Path, source_root: Path = ROOT) -> None:
    (dst / ".lake").mkdir(parents=True, exist_ok=True)
    pk = dst / ".lake" / "packages"
    if not pk.exists():
        pk.symlink_to((source_root / ".lake" / "packages").resolve(), target_is_directory=True)


def copy_build_artifacts(task: Task, dst: Path, source_root: Path = ROOT, *, include_specs: bool = True) -> None:
    """Seed a fresh copy with prebuilt oleans of the case's extraction, Defs, (optionally) Specs, and spec_audit."""
    src_build = source_root / ".lake" / "build"
    mods = [task.defs_module, "Benchmark.SpecAudit"]
    if include_specs:
        mods.append(task.specs_module)
    for sub in ("lib/lean", "ir"):
        base = src_build / sub
        pkg_dir = base / task.lean_package
        if pkg_dir.is_dir():
            shutil.copytree(pkg_dir, dst / ".lake" / "build" / sub / task.lean_package, dirs_exist_ok=True)
        for f in base.glob(task.lean_package + ".*"):
            out = dst / ".lake" / "build" / sub / f.name
            out.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(f, out)
        for mod in mods:
            mod_rel = Path(*mod.split("."))
            mod_parent = (base / mod_rel).parent
            if mod_parent.is_dir():
                for f in mod_parent.glob(mod_rel.name + ".*"):
                    out = dst / ".lake" / "build" / sub / f.relative_to(base)
                    out.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(f, out)
    bin_src = src_build / "bin" / "spec_audit"
    if bin_src.is_file():
        bin_dst = dst / ".lake" / "build" / "bin" / "spec_audit"
        bin_dst.parent.mkdir(parents=True, exist_ok=True)
        if not bin_dst.exists():
            bin_dst.symlink_to(bin_src.resolve())


def copy_pristine(task: Task, dst: Path, source_root: Path = ROOT) -> None:
    for name in ("lakefile.lean", "lake-manifest.json", "lean-toolchain", "Benchmark.lean"):
        src = source_root / name
        if src.is_file():
            shutil.copy2(src, dst / name)
    shutil.copytree(
        source_root / "extracted" / task.lean_package,
        dst / "extracted" / task.lean_package,
        ignore=shutil.ignore_patterns(".lake", "__pycache__"),
    )
    for rel in (task.defs_file, task.specs_file, "Benchmark/SpecAudit.lean"):
        src = source_root / rel
        if src.is_file():
            out = dst / rel
            out.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, out)
    link_lake_packages(dst, source_root)


def check_module(task: Task, submitted_module: str) -> str:
    binders, concl = split_statement(task.spec_signature)
    tp = f"∀ {binders}, {concl}" if binders else concl
    return (
        f"import {task.defs_module}\nimport {submitted_module}\n\n"
        f"{opens_block(task)}\n\n"
        f"namespace {task.namespace}\n\n"
        f"/-- Canonical type of specification `{task.id}`. -/\n"
        f"def rsgb_canonical_type :=\n  {tp}\n\n"
        f"end {task.namespace}\n\n"
        f"noncomputable def {CHECK_NS}.rsgb_check : {task.namespace}.rsgb_canonical_type :=\n"
        f"  @{task.spec_name}\n\n"
        f"#print axioms {CHECK_NS}.rsgb_check\n"
    )


AXIOMS_RE = re.compile(r"depends on axioms: \[(?P<ax>[^\]]*)\]", re.DOTALL)


def parse_axioms(output: str) -> list[str] | None:
    if "does not depend on any axioms" in output:
        return []
    m = AXIOMS_RE.search(output)
    if not m:
        return None
    return [a.strip() for a in m.group("ax").replace("\n", " ").split(",") if a.strip()]


def verify_task(
    task: Task,
    submitted_file: Path,
    *,
    timeout_seconds: int = 900,
    source_root: Path = ROOT,
    keep: bool = False,
) -> VerifyResult:
    started = time.time()
    res = VerifyResult(task.id, task.spec_name, "harness_error")
    try:
        if not submitted_file.is_file():
            res.status, res.detail = "spec_missing", f"{submitted_file} not found"
            return res
        text = submitted_file.read_text(encoding="utf-8")
        res.submitted_sha256 = sha256_text(text)
        fail = policy_failure(task, text, allowed_local_imports=(task.defs_module,))
        if fail:
            res.status, res.detail = fail
            return res
        tmp_base = source_root / ".lake" / "verify_tmp"
        tmp_base.mkdir(parents=True, exist_ok=True)
        tmp = Path(tempfile.mkdtemp(prefix="rsgb-verify-", dir=tmp_base))
        repo = tmp / "repo"
        repo.mkdir()
        try:
            copy_pristine(task, repo, source_root)
            copy_build_artifacts(task, repo, source_root, include_specs=True)
            rel = task.editable_file
            (repo / rel).parent.mkdir(parents=True, exist_ok=True)
            (repo / rel).write_text(text, encoding="utf-8")
            module = task.target_module
            mod_olean = Path(".lake/build/lib/lean") / Path(*module.split(".")).with_suffix(".olean")
            (repo / mod_olean).parent.mkdir(parents=True, exist_ok=True)
            check_dir = repo / "Benchmark" / "VerifierCheck"
            check_dir.mkdir(parents=True, exist_ok=True)
            (check_dir / "Check.lean").write_text(check_module(task, module), encoding="utf-8")
            code, out = run(["lake", "env", "lean", "-o", str(mod_olean), rel], repo, timeout_seconds)
            if code != 0 or re.search(r"\berror\b", out):
                res.status = "timeout" if code == 124 else "lean_check_failed"
                res.detail = compact(out)
                return res
            code, out = run(["lake", "env", "lean", "Benchmark/VerifierCheck/Check.lean"], repo, timeout_seconds)
            if code == 75:
                res.status, res.detail = "verifier_infra_error", "no Lean slot available for the statement check:\n" + out[-2000:]
                return res
            if code == 124:
                res.status, res.detail = "timeout", compact(out)
                return res
            if code != 0:
                res.status = "spec_signature_mismatch" if ("mismatch" in out or "type" in out) else "spec_missing"
                res.detail = compact(out)
                return res
            axioms = parse_axioms(out)
            res.axioms = axioms
            if axioms is None:
                res.status, res.detail = "verifier_infra_error", "could not parse #print axioms output:\n" + out[-2000:]
                return res
            bad = sorted(set(axioms) - TRUSTED_AXIOMS)
            if bad:
                res.status, res.detail = "untrusted_axioms", f"specification depends on untrusted axioms: {bad}"
                return res

            # Step 6: Kernel AST Lowering (`spec_audit`) + Z3 SMT Equivalence Check
            audit_cmd = [
                "lake", "env", ".lake/build/bin/spec_audit",
                task.specs_module,
                module,
                task.oracle_theorem_name,
                task.spec_name,
            ]
            code, audit_out = run(audit_cmd, repo, timeout_seconds)
            if code != 0:
                res.status, res.detail = "audit_error", f"spec_audit failed (exit {code}):\n" + compact(audit_out)
                return res
            # Find last JSON line in audit_out
            json_line = None
            for line in reversed(audit_out.splitlines()):
                sline = line.strip()
                if sline.startswith("{") and sline.endswith("}"):
                    json_line = sline
                    break
            if not json_line:
                res.status, res.detail = "audit_error", f"no JSON output from spec_audit:\n{compact(audit_out)}"
                return res
            audit_data = json.loads(json_line)
            if "error" in audit_data:
                res.status, res.detail = "audit_error", f"spec_audit error: {audit_data['error']}"
                return res

            z3_res = check_spec_equivalence(audit_data, timeout_ms=10000)
            res.soundness = z3_res.soundness
            res.completeness = z3_res.completeness
            res.nonvacuity = z3_res.nonvacuity
            res.nontriviality = z3_res.nontriviality
            res.counterexample = z3_res.counterexample
            res.status = z3_res.status
            res.detail = z3_res.detail
            return res
        finally:
            if not keep:
                shutil.rmtree(tmp, ignore_errors=True)
    except Exception as exc:  # report, never crash the caller
        res.status, res.detail = "harness_error", repr(exc)
        return res
    finally:
        res.duration_seconds = round(time.time() - started, 3)
