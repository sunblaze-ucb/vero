# Curating a Lean 4 Source Repo

A short walkthrough of turning an existing Lean 4 source repository into a benchmark for `vero run`. Pair this with [`src/vero/curation/README.md`](../src/vero/curation/README.md) for the general workflow + CLI reference, and [`pipeline-schema.md`](pipeline-schema.md) for the artifact shapes.

## The principle: honest extraction, never synthesis

Lean→Lean curation is **extraction** of what the source repo already proves, not invention of new specifications. The `lean_spec` pipeline reads existing `theorem` / `lemma` / `example` declarations, reshapes their conclusions into `def spec_<name> (impl : RepoImpl) : Prop` form, and pins them as the benchmark's specs. It does **not** run a `spec_write` stage, since adding LLM-invented specs would dilute the benchmark with claims the upstream repo never made.

If you want more specs than the source provides, extend the upstream repo first (PR new theorems into the source), then re-run curation. Don't paper over a thin source spec set by hand-editing the curated benchmark.

## Quick start

```bash
# From the repo root, with .venv activated.
python -m vero.curation run \
  /path/to/lean-source-repo curation_outputs/<name> \
  --workflow lean_spec --lang lean

# Resume mid-pipeline after a human-review gate
python -m vero.curation run curation_outputs/<name> --stage <next-stage>
```

The `lean_spec` workflow runs:

```
init → discover → select → plan → translate → validate
```

Each stage with `human_review = True` pauses the pipeline; resume by re-running with `--stage <next>` once you've reviewed the artifact.

## Worked example with `lean-regex`

The current ratified Lean curation is `pandaman64/lean-regex@70af0835` (44 source files / 4465 LOC under `regex/Regex/`). Final state: 19 modules · 35 APIs · 29 specs · 0 axioms; `lake build` clean (39 jobs); validator 9/10 pass (the one warn is `source_coverage`, expected since `lean_spec` doesn't write `.vero/discover.json` in the same shape the rule looks for).

Output lives at `curation_outputs/lean_regex/lean_output/Regex/`. That is the lake project root in canonical layout (manifest + lakefile + `Regex.lean` root hub at the top, package source at `Regex/Regex/...`). The benchmark is registered as `conf/benchmark/lean_regex.yaml` so you can run `vero run benchmark=lean_regex agent=...` against it directly.

## What to look for at each human-review gate

### `discover` → check `curation/discovery/*.md`

Each file becomes one markdown checklist. The agent classifies every top-level item as one of: *type* (structure / inductive), *api* (public exec function), *api_helper* (private helper), *theorem* (becomes a candidate spec), *tactic*, *test*. Uncheck anything you don't want in the benchmark (test fixtures, deprecated functions, internal lemmas).

Red flags to watch for:
- Source `theorem` mis-classified as `tactic` or vice versa. The agent's guess on lemmas with non-trivial conclusions sometimes lands wrong.
- API helpers (private / underscore-prefixed) classified as APIs. These inflate the spec target without adding signal.

### `select` → check `curation/selection.md`

Closure of selected items + topological layering. Confirm the layer counts look reasonable (a 19-module project shouldn't have 1 layer, nor 19). The agent flags missing dependencies as warnings, so chase each one before approving.

### `plan` → check `curation/plan.json` (and any `@question` annotations)

The translation plan with exact Lean signatures + bundle wiring. Look for:
- Inline `-- !curation @question`s the agent left for you (translation decisions you need to confirm).
- API signatures that drift from the source (the source is the ground truth, and the agent should not "improve" types).
- `repo_impl_field` naming, which should be lowerCamelCase of the package name, with no fancy substitutions.

### `translate` → check the emitted Lean tree + `curation/review.md`

The agent writes `Impl/`, `Spec/`, `Bundle.lean`, `Harness.lean`, `Test.lean` per the canonical paradigm (see [`reference/BankLedger/`](../reference/BankLedger/)). The Impl bodies should be the **real source code** (not `sorry`). Lean→Lean curation preserves implementations verbatim, and only the specs become benchmark targets.

Look for:
- `lake build` exit code 0 (the stage runs it post-emit; failure surfaces in `review.md`).
- Spec count vs theorem count in the source. If you had 30 theorems but only 12 specs, the agent dropped some, so investigate.
- `!curation @review v1` annotations on each translated item. Fold these into your human feedback by adding `-- !curation @human: <note>` comments inline, then re-run `--stage translate --force`.

### `validate` → check `curation/validate/report.md`

Rule-based + (optional) LLM-review checks: marker grammar, manifest consistency, spec shape (`(impl : RepoImpl) : Prop`, no `theorem`s in `Spec/*.lean`), source coverage. A green `validate` is the bar for shipping the benchmark. Specifically for Lean:

- `manifest_consistency` accepts `noncomputable` / `partial` / `private` / `protected` / `unsafe` modifiers in front of `def`, accepts inline-args shape (`def Name (a : T) : Sig := ...`), and allows `?` / `!` / `'` in spec identifier names. If your Lean source uses any of these and validate flags them, you're on an old branch, so pull main.
- `spec_shape` strips block comments before checking that `Spec/*.lean` has no `theorem` declarations, so docstrings mentioning the word "theorem" don't false-match.

## Known caveats

These are real gaps, not branch-only bugs:

1. **Non-`.lean` data files are dropped**. If the source repo ships data (Unicode case-folding tables, lookup JSON, etc.) the curator emits only the `.lean` tree. For lean-regex we hand-restored `data/Simple_Case_Folding.txt` from upstream after curation. Plan to do the same for any source repo with auxiliary data.
2. **Top-level workspace duplication** can show up in some workflows. If you see two parallel trees at `curation_outputs/<name>/lean_output/`, delete the redundant one and keep the canonical `lean_output/<Project>/` lake root.
3. **Manifest `root_package` may need a hand-fix** to match the lakefile lib name. The validator catches mismatches; for some scaffolds the agent emits a different casing than what the source's `lakefile.toml` declares.
4. **Validator's `source_coverage` rule** looks for `.vero/discover.json` but `lean_spec` writes `curation/discovery_report.json` instead, so this turns into an info-level warn rather than a blocker. Safe to ignore for now.

## Verifying you're done

Before registering the benchmark in `conf/benchmark/<name>.yaml`:

```bash
# From the lake project root (curation_outputs/<name>/lean_output/<Project>/)
lake build
# Should exit 0 with only expected `sorry` warnings, typically zero for
# Lean→Lean since impls are preserved verbatim.

python -m vero.curation status curation_outputs/<name>
# Every stage shows [+]. validate.completed_at is set.

python -m vero.curation extract curation_outputs/<name>/lean_output/<Project>/
# Lists every !benchmark slot with file:line + sorry status.
# Spec/*.lean slots should all be sorry (the proof targets);
# Impl/*.lean code-block slots should be non-sorry (real source).
```

Then add the conf/benchmark entry:

```yaml
# conf/benchmark/<name>.yaml
path: curation_outputs/<name>/lean_output/<Project>
id: <name>
default_mode: proof
```

and smoke-test with the gen/eval tutorial (`docs/gen-eval-tutorial.md`).

## What `lean_spec` is *not* for

- **Benchmarks where you want LLM-invented specs.** Use `python_spec` (Python source) or extend the Lean source first, then `lean_spec`.
- **Benchmarks where the spec set should be smaller than what the source proves.** Use the discover / select stages to drop theorems you don't want. Don't post-edit the manifest.
- **Adding new APIs to an existing curated benchmark.** Re-run from `discover` against the updated source instead of patching by hand.

## Pointers

- General workflow + CLI reference: [`src/vero/curation/README.md`](../src/vero/curation/README.md)
- Artifact schemas: [`pipeline-schema.md`](pipeline-schema.md)
- Canonical benchmark shape: [`reference/BankLedger/`](../reference/BankLedger/)
- Skills the agent loads at each stage: `.claude/skills/vero-{discover,select,plan,translate,source-lean,lean-pitfalls}/SKILL.md`
- Running the curated benchmark: [`gen-eval-tutorial.md`](gen-eval-tutorial.md)
