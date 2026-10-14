# Rust Specification Generation Benchmark (RSGB)

**v1.0, 2026-10-13.** 100 Lean 4 formal specification generation tasks extracted from real-world Rust property-based tests, graded by the Lean 4 kernel and Z3 SMT bidirectional logical equivalence.

## Overview

Each task translates an existing `proptest` (69) or `quickcheck` (31) property test from 33 open-source Rust crates into a Lean 4 specification-synthesis task over the verbatim `cargo hax into lean` (Charon + Aeneas) extraction:

- **Implementation (`extracted/<Package>/`):** Mechanical Lean 4 translation of the crate under test (never hand-edited).
- **Shared Domain Helpers (`Benchmark/Cases/<Project>/<Case>/Defs.lean`):** Visible to the agent; provides shared domain types, constants, and non-spec test-model helpers.
- **Hidden Oracle Specifications (`Benchmark/Cases/<Project>/<Case>/Specs.lean`):** Hidden from the agent workspace (`Benchmark.Cases.<Project>.<Case>.Oracle`); contains the ground-truth `OracleSpec` and domain preconditions `Pre`.
- **Editable Task (`Benchmark/Generated/<Project>/<Case>/Tasks/<Task>.lean`):** One editable Lean 4 file per task containing `def <spec_name> <binders> : Prop := True`.
- **Splits:** 21 easy, 47 medium, 32 hard across integer and big-number arithmetic, encodings, bit manipulation, checksums, finite fields, parsers, containers, and search.

## Grading (Lean 4 Kernel + Z3 SMT Equivalence)

`python -m rsgb.verify <task_id> <file.lean>` passes a submitted specification iff all 6 checks succeed:

1. **Static Policy (`rsgb/policy.py`):** No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `#eval`, syntax extensions, or hidden imports (`Specs` / `References`); specification signature and namespace unchanged.
2. **Lean 4 Kernel Elaboration (`rsgb/verifier.py`):** Compiles in a clean copy of the benchmark and matches the canonical specification type `∀ <binders>, Prop` definitionally in a separate check module.
3. **Axiom Audit (`#print axioms`):** Depends only on `propext`, `Classical.choice`, and `Quot.sound`.
4. **Kernel AST Lowering (`Benchmark/SpecAudit.lean`):** Inspects the elaborated Lean 4 `Environment`, unfolds helper definitions, symbolically evaluates the `RustM` weakest-precondition monad (`⦃ ... ⦄`, `Bind.bind`, `lift`, checked arithmetic, `Option`/`Result`/`Ordering` eliminators, finite array indexing), and lowers both `OracleSpec` and `CandidateSpec` under the task's domain preconditions `Pre`.
5. **Non-Vacuity & Non-Triviality (`rsgb/z3_spec.py`):**
   - **Non-Vacuity (`SAT`):** $\exists \vec{x},\; \text{Pre}(\vec{x}) \land \text{CandidateSpec}(\vec{x})$ is satisfiable (rejects contradictory specs such as `False`, which fails `100/100` tasks as `vacuous_spec`).
   - **Non-Triviality (`SAT`):** $\exists \vec{x},\; \text{Pre}(\vec{x}) \land \neg\text{CandidateSpec}(\vec{x})$ is satisfiable (rejects tautological specs such as `True`, which fails `100/100` tasks as `trivial_spec`).
6. **Bidirectional Semantic Equivalence (`rsgb/z3_spec.py`):**
   - **Soundness (`UNSAT`):** $\text{Pre}(\vec{x}) \land \text{CandidateSpec}(\vec{x}) \land \neg\text{OracleSpec}(\vec{x})$ is unsatisfiable.
   - **Completeness (`UNSAT`):** $\text{Pre}(\vec{x}) \land \text{OracleSpec}(\vec{x}) \land \neg\text{CandidateSpec}(\vec{x})$ is unsatisfiable.

## Validation & Pilot Results

### Verifier Calibration (100/100 Tasks)

| Suite | Tasks | Verdict | Details |
|---|---:|---|---|
| Reference Specifications (`Benchmark/Cases/*/*/References/*.lean`) | 100/100 | **100/100 `passed`** | `soundness=unsat`, `completeness=unsat`, `nonvacuity=sat`, `nontriviality=sat` |
| Trivial Tautology Mutation (`True`) | 100/100 | **100/100 rejected (`trivial_spec`)** | `0%` false positives |
| Vacuous Contradiction Mutation (`False`) | 100/100 | **100/100 rejected (`vacuous_spec`)** | `0%` false positives |

### Agent Pilot Evaluation (10 Representative Tasks Across 10 Crates)

Evaluated with the tool-calling agent (`rsgb.run_agent`) on a 10-task cross-crate stratification (`arxid`, `crc32fast`, `crypto_bigint`, `fastdivide`, `goldilocks`, `plonky3`, `sigma_ser`, `succinct`, `tinyset`, `use_combinatorics`):

| Model | Provider ID | Verified (`passed`) | Unsound (`unsound_spec`) | Incomplete (`incomplete_spec`) | Trivial / Vacuous |
|---|---|---:|---:|---:|---:|
| Z.ai GLM 5.3 Flash | `zai/glm-5.3-flash` | **10/10 (100%)** | 0 | 0 | 0 |
| Gemini 3 Flash | `gemini-3-flash` | **10/10 (100%)** | 0 | 0 | 0 |

## Usage

Requires `elan`, `git`, Python >= 3.10, and `z3-solver`.

```sh
lake exe cache get && lake build Benchmark spec_audit
python -m rsgb.verify <task_id> spec.lean            # JSON verdict + Z3 counterexample; exit code 0 iff passed
python -m rsgb.check_references --jobs 4             # verify all 100 reference specs (expect 100/100 passed)
python -m rsgb.check_references --skeletons --jobs 4 # verify all 100 blank templates fail (expect 100/100 rejected)
python -m rsgb.run_agent --model M --base-url URL --api-key-env VAR --tasks all
```

## Layout

```text
tasks.jsonl                                              100 task definitions and metadata
extracted/<Package>/                                     verbatim cargo-hax Lean extractions
Benchmark/SpecAudit.lean                                 Lean 4 kernel AST lowerer for Z3 equivalence
Benchmark/Cases/<Project>/<Case>/Defs.lean               shared non-spec domain helpers (visible to agent)
Benchmark/Cases/<Project>/<Case>/Specs.lean              hidden ground-truth OracleSpec + preconditions
Benchmark/Cases/<Project>/<Case>/References/<Task>.lean  100 reference specifications
Benchmark/Generated/<Project>/<Case>/Tasks/<Task>.lean   100 editable specification templates
rust/<project>/<case>/                                   pinned upstream Rust sources & property tests
rsgb/ (and rfvb/)                                        verifier, Z3 equivalence engine, and agent runner
```

Pinned toolchain: Lean `v4.31.0`, Mathlib, Aeneas `build-183e4f0`, `hax-lean v0.3.27`, `cargo-hax 0.4.1`, `z3-solver 4.13.3`.

## License

Benchmark code, specifications, task files, and verifier are licensed under Apache-2.0. Files under `rust/` and `extracted/` retain their upstream licenses (MIT, Apache-2.0, Unlicense, or CC0).
