"""Extract a real upstream crate into the benchmark with cargo-hax (Charon + Aeneas).

  python -m rfvb.extract_crate --name datealgo/core --repo https://github.com/nakedible/datealgo-rs \
      --rev <sha|branch> [--subdir path/to/crate] --start-from datealgo [--start-from ...] \
      [--cargo-args "--no-default-features"] [--charon-args "..."]

Steps: clone the repository at the given revision (the resolved commit SHA is
recorded), drop benches / examples / dev-dependencies from the manifest (they
are not needed and often fail to resolve), run `cargo hax into lean` with
`--start-from` items, copy the generated `Extraction/` and `Assumptions/`
modules into `extracted/<Pkg>/` under the benchmark's module prefix, copy the
crate's sources (src/, manifest, license, readme, tests) into
`rust/<project>/<case>/`, register the package in `lakefile.lean` and record the
provenance in `v2/sources.jsonl`. Code is never hand-edited.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from . import ROOT

WORK = Path(os.environ.get("RSGB_HAX_WORK", str(Path.home() / "hax-work")))


def camel(s: str) -> str:
    return "".join(p[:1].upper() + p[1:] for p in re.split(r"[^A-Za-z0-9]+", s) if p)


def run(cmd: list[str], cwd: Path, timeout: int = 3600) -> subprocess.CompletedProcess:
    env = dict(os.environ)
    env["PATH"] = f"{Path.home() / '.cargo/bin'}:{env.get('PATH', '')}"
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout, env=env)


def clean_manifest(path: Path, default_features: str | None = None) -> None:
    text = path.read_text(encoding="utf-8")
    if default_features is not None:
        # charon runs its own cargo invocation: select features through the manifest's `default`
        feats = ", ".join(f'"{f}"' for f in default_features.split(",") if f)
        if re.search(r"^default\s*=", text, re.M):
            text = re.sub(r"^default\s*=\s*\[[^\]]*\]", f"default = [{feats}]", text, flags=re.M | re.S)
        elif "[features]" in text:
            text = text.replace("[features]", f"[features]\ndefault = [{feats}]", 1)
    # remove [[bench]] / [[example]] / [[test]] tables and dev-dependencies sections
    out, skip = [], False
    for line in text.splitlines():
        s = line.strip()
        if s.startswith("["):
            skip = bool(re.match(r"^\[\[(bench|example|test)\]\]$", s)) or bool(
                re.match(r"^\[(target\.[^\]]*\.)?dev-dependencies(\.[^\]]*)?\]$", s))
        if not skip:
            out.append(line)
    path.write_text("\n".join(out) + "\n", encoding="utf-8")


def register_lakefile(pkg: str) -> None:
    """Append `.submodules `<pkg>` to the globs of the `Extracted` library."""
    lf = ROOT / "lakefile.lean"
    text = lf.read_text(encoding="utf-8")
    if f".submodules `{pkg}" in text:
        return
    m = re.search(r"lean_lib Extracted where.*?globs := #\[(.*?)\n  \]", text, re.S)
    if not m:
        raise RuntimeError("cannot find the Extracted globs in lakefile.lean")
    body = m.group(1).rstrip() + f",\n    .submodules `{pkg}"
    text = text[:m.start(1)] + body + text[m.end(1):]
    lf.write_text(text, encoding="utf-8")


def extract(name: str, repo: str, rev: str, subdir: str, start_from: list[str], cargo_args: str,
            charon_args: str, pkg: str | None, default_features: str | None = None) -> dict:
    project, case = name.split("/")
    pkg = pkg or camel(project) + camel(case)
    src = WORK / f"{project}__{case}"
    if not (src / ".git").is_dir():
        if src.exists():
            shutil.rmtree(src)
        r = run(["git", "clone", "-q", repo, str(src)], WORK)
        if r.returncode:
            raise RuntimeError(r.stderr)
    r = run(["git", "checkout", "-q", "-f", rev], src)
    if r.returncode:
        raise RuntimeError(r.stderr)
    run(["git", "clean", "-fdxq"], src)
    sha = run(["git", "rev-parse", "HEAD"], src).stdout.strip()
    crate = src / subdir if subdir else src
    clean_manifest(crate / "Cargo.toml", default_features)
    # workspace roots also carry dev-dependencies / benches
    if subdir and (src / "Cargo.toml").is_file():
        clean_manifest(src / "Cargo.toml")
    shutil.rmtree(crate / "proofs", ignore_errors=True)
    cmd = ["cargo", "hax"]
    if cargo_args:
        cmd += ["-C", *shlex.split(cargo_args), ";"]
    sf = " ".join(f"--start-from {s}" for s in start_from)
    cmd += ["into", "lean", f"--charon-args={sf} {charon_args}".strip()]
    r = run(cmd, crate)
    log = (r.stdout + r.stderr)[-6000:]
    gen = sorted(p for p in (crate / "proofs" / "lean").glob("*/Extraction") if p.is_dir()) \
        if (crate / "proofs" / "lean").is_dir() else []
    if not gen or not (gen[0] / "Funs.lean").is_file():
        return {"name": name, "ok": False, "stage": "hax", "log": log}
    # Aeneas reports unsupported bodies but still writes the package (those bodies become
    # axioms); keep the extraction and record how many bodies were lost.
    errlog = crate / "proofs" / "lean" / "aeneas-error.log"
    errtext = (errlog.read_text(errors="replace") if errlog.is_file() else "") + log
    ignored = re.findall(r"Ignoring the body of '([^']+)'", errtext) + \
        re.findall(r"Could not translate the body of function '([^']+)'", errtext)
    gen_dir = gen[0].parent
    gen_pkg = gen_dir.name
    dst = ROOT / "extracted" / pkg
    if dst.exists():
        shutil.rmtree(dst)
    for sub in ("Extraction", "Assumptions"):
        if (gen_dir / sub).is_dir():
            shutil.copytree(gen_dir / sub, dst / sub,
                            ignore=shutil.ignore_patterns("*_Template.lean"))
    # When aeneas exits early hax only writes the *_Template.lean seeds of the external modules;
    # recreate the layout of a successful run (Assumptions/<X>.lean seeded, Extraction/<X>.lean imports it).
    for ext in ("FunsExternal", "TypesExternal"):
        tmpl = gen_dir / "Extraction" / f"{ext}_Template.lean"
        if tmpl.is_file() and not (dst / "Extraction" / f"{ext}.lean").is_file():
            (dst / "Assumptions").mkdir(parents=True, exist_ok=True)
            if not (dst / "Assumptions" / f"{ext}.lean").is_file():
                shutil.copy2(tmpl, dst / "Assumptions" / f"{ext}.lean")
            (dst / "Extraction" / f"{ext}.lean").write_text(f"import {gen_pkg}.Assumptions.{ext}\n", encoding="utf-8")
    if (gen_dir / "Extraction.lean").is_file():
        shutil.copy2(gen_dir / "Extraction.lean", dst / "Extraction.lean")
    else:  # hax writes the umbrella last; recreate it when aeneas stopped early
        mods = [m for m in ("Types", "Funs") if (dst / "Extraction" / f"{m}.lean").is_file()]
        (dst / "Extraction.lean").write_text(
            "-- Imports the extraction modules.\n" + "".join(f"import {gen_pkg}.Extraction.{m}\n" for m in mods),
            encoding="utf-8")
    for f in dst.rglob("*.lean"):
        t = f.read_text(encoding="utf-8")
        t = re.sub(rf"\bimport {re.escape(gen_pkg)}\.", f"import {pkg}.", t)
        f.write_text(t, encoding="utf-8")
    rust_dst = ROOT / "rust" / project / case
    if rust_dst.exists():
        shutil.rmtree(rust_dst)
    rust_dst.mkdir(parents=True)
    for item in ("src", "tests", "Cargo.toml", "README.md", "LICENSE", "LICENSE-MIT", "LICENSE-APACHE", "COPYING"):
        p = crate / item
        if p.is_dir():
            shutil.copytree(p, rust_dst / item)
        elif p.is_file():
            shutil.copy2(p, rust_dst / item)
    for lic in src.glob("LICENSE*"):
        if not (rust_dst / lic.name).exists():
            shutil.copy2(lic, rust_dst / lic.name)
    import fcntl
    lockf = open(ROOT / ".lake" / "registry.lock", "w")
    fcntl.flock(lockf, fcntl.LOCK_EX)  # lakefile.lean / sources.jsonl are shared by parallel authors
    register_lakefile(pkg)
    prov = {"name": name, "package": pkg, "repo": repo, "commit": sha, "subdir": subdir,
            "start_from": start_from, "cargo_args": cargo_args, "charon_args": charon_args,
            "default_features": default_features,
            "hax": "0.4.1", "extracted_at": datetime.now(timezone.utc).isoformat(timespec="seconds")}
    sources = ROOT / "v2" / "sources.jsonl"
    rows = [json.loads(l) for l in sources.read_text().splitlines() if l.strip()] if sources.is_file() else []
    rows = [x for x in rows if x["name"] != name] + [prov]
    sources.write_text("".join(json.dumps(x) + "\n" for x in rows), encoding="utf-8")
    lockf.close()
    n_defs = len(re.findall(r"^(?:@\[[^\]]*\]\s*)*def\b", (dst / "Extraction" / "Funs.lean").read_text(), re.M)) \
        if (dst / "Extraction" / "Funs.lean").is_file() else 0
    n_ax = sum(len(re.findall(r"^axiom\s", f.read_text(), re.M)) for f in (dst / "Assumptions").glob("*.lean")) \
        if (dst / "Assumptions").is_dir() else 0
    return {"name": name, "ok": True, "package": pkg, "commit": sha, "defs": n_defs, "axioms": n_ax,
            "hax_exit": r.returncode, "ignored_bodies": sorted(set(ignored))}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python -m rfvb.extract_crate")
    ap.add_argument("--name", required=True, help="<project>/<case>")
    ap.add_argument("--repo", required=True)
    ap.add_argument("--rev", default="HEAD")
    ap.add_argument("--subdir", default="")
    ap.add_argument("--start-from", action="append", required=True)
    ap.add_argument("--cargo-args", default="")
    ap.add_argument("--charon-args", default="")
    ap.add_argument("--package")
    ap.add_argument("--default-features", help="comma list that replaces the crate's default features "
                    "(empty string = no default features)")
    a = ap.parse_args(argv)
    WORK.mkdir(parents=True, exist_ok=True)
    res = extract(a.name, a.repo, a.rev, a.subdir, a.start_from, a.cargo_args, a.charon_args, a.package, a.default_features)
    print(json.dumps(res, indent=1))
    return 0 if res["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
