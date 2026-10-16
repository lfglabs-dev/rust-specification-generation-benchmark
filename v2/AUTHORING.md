# Authoring a v2 target (gold specification + bug zoo)

A v2 target asks an agent to *design* a specification for a small public API of a
crate. The agent never sees the files described here. Grading needs, per target:

1. `v2/targets/<project>__<case>.json` — metadata (below).
2. `Benchmark/V2/<Project>/<Case>/Gold.lean` — the hidden **gold specification**:
   `def gold_<name> (inputs…) : Prop` properties plus `def diff_<name> (inputs…)`
   probes. Same namespace layout as `Benchmark/V2/Arxid/Permute/Gold.lean`
   (read it first; it is the reference example).
3. Optional hand-written bugs (`manual_mutants` in the JSON).

## The gold specification

The gold spec defines *what matters*: a mutant of the implementation only counts
for grading if it violates at least one gold property. So the gold spec must be

- **true**: every `gold_*` holds for all inputs on the real implementation
  (checked on thousands of generated inputs by `check-gold`/`prepare`);
- **the intended contract, as complete as you can make it**: what the
  documentation, names, types and code make clear a careful engineer would
  state. Cover every API function: exact results against a simple mathematical
  model (written independently of the implementation, e.g. with `Nat`/`Int`
  arithmetic, `List` functions, Mathlib), inverse/round-trip relations, algebraic
  laws, ranges and invariants, edge cases, and **exact panic / error conditions**
  (Rust debug semantics: overflow, division by zero, out-of-bounds, `assert!`
  all give `fail .panic`; state both "panics iff …" directions where feasible);
- **not tied to incidental details** that the docs do not promise (for example
  exact pseudo-random output values of a hash/cipher, unless documented as
  stable test vectors). Mutants that only change such details then count as
  "unspecified" and are excluded from grading.
- Avoid copying the implementation line by line; a reference model should be the
  simplest obviously-correct definition (e.g. `List`-based or arithmetic).

The original v1 benchmark's oracle properties for the case
(`Benchmark/Cases/<Project>/<Case>/Specs.lean`, namespace `…Oracle`, with
hypotheses in the `axiom` statements) are the crate's own property tests: the gold
spec should *include* their content and go well beyond it.

### Executability (same rules as candidates)
Properties are executed by `#rsgb_test` (`Benchmark/Exec/Driver.lean`): inputs are
the explicit binders, sampled by `Plausible.Arbitrary` instances
(`Benchmark/Exec/Runtime.lean`: Rust scalars biased to edge values / log-uniform,
`Bool`, `List`/`Slice`/`Vec`/`Std.Array` with short lengths, pairs). The body must be
decidable by evaluation: `⦃ ⦄`, `=`/`≠` (incl. on `RustM` values), `<`, `≤`, `∧`,
`∨`, `¬`, `→`, `if`, bounded `∀ i < n`, `∀ x ∈ l`, computable helpers. `Prop`
helpers defined in the file are unfolded automatically. Restrict ranges with small
input types + `RSGB.mkU .U32 w.val` / `RSGB.mkI .I64 z` (from `Benchmark/V2/Prelude.lean`).
Guard loop bounds with preconditions so evaluation terminates quickly.
If a crate struct type is an input, add `deriving instance Plausible.Arbitrary for T`
(and `Repr`) in Gold.lean — but candidates cannot do this unless you mention the
type in `extra_types_note` and put the instance in a shared module; prefer scalar
inputs and construct structs inside the property.

### Differential probes
`def diff_<name> (inputs…) := <api call>` (any number). They define how mutants
are compared with the original (outputs on 400 shared random inputs). Map inputs
into ranges where the call terminates quickly (e.g. `% 25` on loop counts). Cover
every API function.

## Hand-written bugs (`manual_mutants`)
3–8 plausible regressions per target that keep the *obvious* property intact but
break a specific, less obvious part of the contract (e.g. mask not applied to
out-of-domain input; off-by-one at a boundary; panic check removed; wrong
behaviour only for negative numbers / empty input / the maximum value). Each is
a single-line edit of `extracted/<Package>/Extraction/Funs.lean`:

```json
{"decl": "arxid.permute.obfuscate", "before": "<exact line, trimmed>", "after": "<replacement line>", "note": "why"}
```

`before` must match exactly one (trimmed) line in the body of `decl`. The edited
file must still compile. Every manual mutant must end up `relevant` (observably
different and violating some gold property) — otherwise strengthen the gold spec
or drop the mutant.

## Target JSON

```json
{
 "id": "arxid/permute",                       // <project>/<case> of the v1 case
 "package": "ArxidPermute",                   // Lean package under extracted/
 "module_prefix": "Benchmark.V2.Arxid.Permute",
 "rust_dir": "rust/arxid/permute",
 "api": ["arxid.permute.obfuscate", ...],     // public functions to specify (Lean names)
 "mutation_roots": [...],                     // usually = api; mutants are drawn from these and their callees
 "forbidden_constants": [...],                // private helpers the candidate may not call (Lean names)
 "allowed_imports": ["ArxidPermute.Extraction"],
 "opens": ["arxid"],                          // namespaces opened in the candidate template
 "upstream_imports": ["Benchmark.Cases.Arxid.Permute.Specs"],
 "upstream_props": ["Benchmark.Cases.Arxid.Permute.Oracle.round_trip_over_the_whole_domain", ...],
 "intent": "Specify the public ... API of `crate::module`: `f`, `g`, ...",
 "manual_mutants": [...]
}
```

`intent` names the API to specify and nothing else: never mention properties,
expected relations or edge cases (that is the agent's job).

## Commands (run from the repository root)

```sh
python3 -m rfvb.v2 check-gold <id>             # build + truth-test gold, run probes
python3 -m rfvb.v2 prepare <id> --jobs 2        # mutants -> status summary
python3 -m rfvb.v2 baseline <id> --jobs 2       # how much the upstream tests catch
```

`prepare` prints `{status: count}`; inspect `.lake/v2cache/<slug>/mutants.json`.
Aim for ≥ 25 relevant mutants spanning several gold-kill signatures, all manual
mutants relevant, and an upstream baseline clearly below 100% class score when
the contract has aspects the crate's tests miss.

## Sibling implementations (`sibling_mutants`) — over-specification check

Agents can read the implementation, so a dominant but worthless strategy is to
*transcribe* it into a model that pins every incidental detail. A great
specification states what the API promises and nothing more. To reward that,
list 1–4 **sibling implementations** where the contract leaves freedom: edits
(same format as `manual_mutants`, multi-edit allowed) that produce a *different
but equally valid* implementation — e.g. a different hash/mixing constant that
the docs do not promise, a different but valid choice among several correct
answers (which index among equal elements, which pivot, tie-breaking, the order
of an unordered result, the value of an unspecified field, a different but
valid error variant only if the docs leave it open).

`prepare` checks that every sibling satisfies **all** gold properties (otherwise
it fails: either the sibling is not valid or the gold spec over-specifies). At
grading, a candidate property that is false on any sibling is dropped as
over-specified. Do not add siblings when the contract is fully determined
(byte layouts, exact arithmetic, documented test vectors).
