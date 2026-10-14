"""Static submission policy (run before any Lean process sees the file)."""
from __future__ import annotations

import re

from .tasks import Task

# Tokens that are never allowed in a submitted specification file (checked with
# comments and string literals stripped). Axiom usage is additionally audited
# semantically with `#print axioms` after the build.
FORBIDDEN_TOKENS = [
    "sorry", "admit", "axiom", "native_decide", "ofReduceBool", "ofReduceNat",
    "implemented_by", "extern", "unsafe", "run_cmd", "run_elab", "run_meta",
    "initialize", "builtin_initialize",
]
FORBIDDEN_RE = re.compile(r"(?<![A-Za-z0-9_'.])(" + "|".join(map(re.escape, FORBIDDEN_TOKENS)) + r")(?![A-Za-z0-9_'])")
# Syntax-extension commands could change how the canonical specification parses.
META_COMMANDS = [
    "macro_rules", "macro", "syntax", "elab_rules", "elab", "notation", "infixl", "infixr",
    "infix", "prefix", "postfix", "declare_syntax_cat", "binder_predicate", "open_notation",
]
META_COMMAND_RE = re.compile(
    r"(?:^|\n)[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:local|scoped|private|protected)[ \t]+)*(" + "|".join(META_COMMANDS) + r")(?![A-Za-z0-9_'])"
)
FORBIDDEN_COMMANDS_RE = re.compile(r"(#eval|#exit|#guard_msgs|set_option\s+debug\.|set_option\s+backward\.|attribute\s*\[\s*-?\s*instance|@\[\s*csimp)")

ALLOWED_IMPORT_PREFIXES = ("Mathlib", "Aeneas", "CoreModels", "Hax", "Std", "Batteries", "Aesop", "Qq", "Plausible", "Init")

IMPORT_RE = re.compile(r"^\s*import\s+(.+)$", re.MULTILINE)


def strip_comments_and_strings(text: str) -> str:
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            if text[i] == "\n":
                out.append("\n")
            i += 1
            continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            out.append('""')
            i = j + 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def split_statement(statement: str) -> tuple[str, str]:
    """Split `binders : conclusion` at the first depth-0 colon."""
    depth = 0
    opens, closes = "([{⦃⟨", ")]}⦄⟩"
    for i, ch in enumerate(statement):
        if ch in opens:
            depth += 1
        elif ch in closes:
            depth -= 1
        elif ch == ":" and depth == 0 and not statement.startswith(":=", i):
            return statement[:i].strip(), statement[i + 1 :].strip()
    raise ValueError("statement has no top-level ':'")


def normalize(text: str) -> str:
    return " ".join(text.split())


def spec_signatures(text: str, decl: str) -> list[str]:
    """All `(noncomputable )?def <decl> ... :=` headers in the (comment-stripped) text."""
    pattern = re.compile(
        rf"(?<![A-Za-z0-9_'.])(?:noncomputable\s+)?def\s+{re.escape(decl)}(?![A-Za-z0-9_'])(?P<sig>.*?):=",
        re.DOTALL,
    )
    return [normalize(m.group("sig")) for m in pattern.finditer(text)]


def policy_failure(task: Task, text: str, *, allowed_local_imports: tuple[str, ...]) -> tuple[str, str] | None:
    code = strip_comments_and_strings(text)
    for line in IMPORT_RE.findall(code):
        for module in line.split():
            if module in allowed_local_imports:
                continue
            if module.split(".")[0] in ALLOWED_IMPORT_PREFIXES:
                continue
            return "hidden_import", f"import {module} is not allowed"
    m = FORBIDDEN_RE.search(code)
    if m:
        return "forbidden_placeholder", f"forbidden token `{m.group(1)}`"
    m = META_COMMAND_RE.search(code)
    if m:
        return "forbidden_placeholder", f"forbidden syntax-extension command `{m.group(1)}`"
    m = FORBIDDEN_COMMANDS_RE.search(code)
    if m:
        return "forbidden_placeholder", f"forbidden command `{m.group(1)}`"
    sigs = spec_signatures(code, task.spec_decl_name)
    if not sigs:
        return "spec_missing", f"no `def {task.spec_decl_name}` found"
    if len(sigs) > 1:
        return "spec_signature_mismatch", f"`def {task.spec_decl_name}` declared {len(sigs)} times"
    if sigs[0] != normalize(task.spec_signature):
        return "spec_signature_mismatch", "specification signature differs from the canonical task signature"
    if f"namespace {task.namespace}" not in code:
        return "spec_signature_mismatch", f"specification must stay in namespace {task.namespace}"
    return None
