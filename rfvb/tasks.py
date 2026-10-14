"""Task loader: reads `tasks.jsonl` (one JSON object per task) at the repo root."""
from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path

from . import ROOT

TASKS_FILE = ROOT / "tasks.jsonl"

HEADER_OPENS = (
    "open CoreModels Aeneas Aeneas.Std.WP\n"
    "open Aeneas.Std hiding namespace core alloc\n"
    "open RustM"
)


@dataclass(frozen=True)
class Task:
    id: str  # <project>/<case>/<task>
    difficulty: str
    property_class: str
    category: str
    theorem_name: str
    theorem_statement: str
    oracle_theorem_name: str
    spec_name: str
    spec_decl_name: str
    spec_signature: str
    spec_noncomputable: bool
    namespace: str
    opens: tuple[str, ...]
    lean_package: str
    defs_module: str
    defs_file: str
    specs_module: str
    specs_file: str
    editable_file: str
    target_module: str
    reference_file: str
    reference_module: str
    implementation_files: tuple[str, ...]
    rust_dir: str
    raw: dict = field(default_factory=dict, compare=False, repr=False)

    @property
    def decl_name(self) -> str:
        return self.spec_decl_name

    @classmethod
    def from_row(cls, row: dict) -> "Task":
        return cls(
            id=row["id"],
            difficulty=row["difficulty"],
            property_class=row["property_class"],
            category=row["category"],
            theorem_name=row["theorem_name"],
            theorem_statement=row["theorem_statement"],
            oracle_theorem_name=row["oracle_theorem_name"],
            spec_name=row["spec_name"],
            spec_decl_name=row["spec_decl_name"],
            spec_signature=row["spec_signature"],
            spec_noncomputable=bool(row.get("spec_noncomputable", False)),
            namespace=row["namespace"],
            opens=tuple(row.get("opens") or ()),
            lean_package=row["lean_package"],
            defs_module=row["defs_module"],
            defs_file=row["defs_file"],
            specs_module=row["specs_module"],
            specs_file=row["specs_file"],
            editable_file=row["editable_file"],
            target_module=row["target_module"],
            reference_file=row["reference_file"],
            reference_module=row["reference_module"],
            implementation_files=tuple(row["implementation_files"]),
            rust_dir=row["rust_dir"],
            raw=row,
        )


def load_tasks(path: Path = TASKS_FILE) -> list[Task]:
    return [Task.from_row(json.loads(line)) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def select_tasks(spec: str | None = None, path: Path = TASKS_FILE) -> list[Task]:
    """Select tasks by a comma-separated list of task ids, `all`,
    `easy`/`medium`/`hard`, or a path to a file with one task id per line."""
    tasks = load_tasks(path)
    if not spec or spec == "all":
        return tasks
    p = Path(spec)
    if p.is_file():
        wanted = [l.strip() for l in p.read_text().splitlines() if l.strip() and not l.startswith("#")]
    else:
        wanted = [s.strip() for s in spec.split(",") if s.strip()]
    by_id = {t.id: t for t in tasks}
    out: list[Task] = []
    for w in wanted:
        if w in by_id:
            out.append(by_id[w])
        elif w in ("easy", "medium", "hard"):
            out.extend(t for t in tasks if t.difficulty == w)
        else:
            raise KeyError(f"unknown task or selector: {w}")
    seen: set[str] = set()
    return [t for t in out if not (t.id in seen or seen.add(t.id))]


def get_task(task_id: str, path: Path = TASKS_FILE) -> Task:
    for t in load_tasks(path):
        if t.id == task_id:
            return t
    raise KeyError(f"unknown task id: {task_id}")


def opens_block(task: Task) -> str:
    return "\n".join([HEADER_OPENS] + [f"open {o}" for o in task.opens])
