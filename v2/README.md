# RSGB v2 — specification *design* benchmark

v1 asked a model to translate one given property (its English docstring, the
literal `prop_assert!` expression and the preconditions were all in the
prompt) into Lean, and graded it by Z3 equivalence with a hidden reference
modulo uninterpreted functions. That measures translation, and the equivalence
check also rejects correct specifications whose shape differs from the
reference (see "v1 issues" below).

v2 asks a model to **design** a specification for a small public API of a real
crate, without being told any property:

> Specify the public API `obfuscate`, `deobfuscate`, `feistel_n`, `feistel_n_inv`
> of `arxid::permute`.

The model reads the (Aeneas-extracted) Lean code and the Rust sources and docs
(with the crate's tests removed), runs experiments with `eval_expr`, checks its
properties with `test_spec`, and submits any number of properties
`def prop_<name> (inputs…) : Prop`.

## Grading: truth × strength, not equivalence

1. **Truth.** Every property is *executed* on 3000 generated inputs against the
   real implementation (the extraction compiled to code; Rust debug semantics:
   overflow / out-of-bounds / assertion failure = panic). One false property
   ⇒ score 0. Properties that cannot be executed are ignored.
2. **No over-specification.** For targets whose contract leaves freedom, hidden
   *sibling implementations* (valid alternatives: different unpromised
   constants, tie-breaking, …) must also satisfy each property; a property
   that fails on a sibling is dropped. This defeats "transcribe the code".
3. **Strength.** The properties are run against hidden *mutants* of the
   implementation: automatically generated single-site mutations (operators,
   constants, comparisons, panic checks, endianness, …) of the API functions
   and everything they call, plus 3–8 hand-written plausible regressions per
   target. A mutant counts only if it is observably different from the
   original (differential testing on probes) **and** violates the hidden gold
   specification, i.e. it breaks the intended contract. The score is the
   fraction of such mutants that the candidate rejects, averaged over
   behavioural classes (mutants grouped by which gold properties they violate),
   so that "breaks everything" bugs and one subtle contract aspect weigh the
   same.

Scores are continuous in [0, 1], so a benchmark-wide 100% requires a
specification at least as discriminating as the gold spec on every target.

## Tracks

- **white-box** (default): the implementation is visible.
- **black-box** (`--mode blackbox`): function bodies are hidden (Rust and Lean);
  the model must infer the contract from documentation and experiments.

## Layout

```text
v2/targets/<project>__<case>.json         target metadata (API, mutation roots, manual bugs, siblings)
Benchmark/V2/<Project>/<Case>/Gold.lean   hidden gold spec (gold_*) + differential probes (diff_*)
Benchmark/V2/Prelude.lean                 helpers available to candidates (RSGB.mkU / mkI)
Benchmark/Exec/Runtime.lean               generators, Decidable instances, test loop
Benchmark/Exec/Driver.lean                #rsgb_test / #rsgb_kill / #rsgb_outputs commands
rfvb/exec.py                              executable copy of the benchmark (.lake/exec)
rfvb/mutate.py                            mutation operators, mutant builds (olean shadowing)
rfvb/v2.py                                prepare / grade / baseline
rfvb/v2_agent.py, rfvb/run_v2.py          agent harness and runner
rfvb/prompts/PROMPT_V2.md                 system prompt
v2/AUTHORING.md                           how to author a target
```

## Usage

```sh
python3 -m rfvb.exec sync && (cd .lake/exec && lake build Extracted Benchmark.Exec.Driver)
python3 -m rfvb.v2 prepare all                      # build + classify mutants (cached in .lake/v2cache)
python3 -m rfvb.v2 baseline all                     # score the crate's own property tests
python3 -m rfvb.v2 grade <target> Candidate.lean
python3 -m rfvb.run_v2 --model M --base-url URL --api-key-env VAR --targets all [--mode blackbox]
python3 -m rfvb.summarize_v2 results/<run>.jsonl [--by target]
```
