---
name: vero-validate
description: Use during the validate stage to produce the LLM-review half of validate.json. Semantic checks (spec intent, idiom, test meaningfulness, review-annotation sanity, spec completeness, repo issue taxonomy) run as tightly-scoped subagent calls against the translated benchmark tree.
allowed-tools: Read, Grep, Glob, Bash
---

# VCG Validate: LLM Review

The validate stage of the curation pipeline has two halves:

1. **Rule-based** (Python, deterministic): eight checks implemented in
   `src/vero/curation/validation/checks.py`. These cover schema,
   markers, file roles, build, toolchain, `#guard`.
2. **LLM review** (this skill): semantic checks that need judgment
   — does the spec capture intent, is the code idiomatic, are tests
   meaningful, etc., and what repo-specific issue patterns should feed
   future validation memory.

**Use this skill only for the LLM-review half.** Rule-based checks
never call the LLM.

**Reference the canonical shape** at `reference/BankLedger/`. Every
check compares the candidate against that shape.

## Input

The subagent is handed:

- `benchmark_path` — absolute path to the translated Lean project
  (contains `manifest.json`, `lakefile.toml`, `<Project>.lean`,
  `<Project>/Impl/`, `<Project>/Spec/`, etc.).
- `check_name` — which semantic review to run.
- `reference_path` — absolute path to `reference/BankLedger/` (the
  canonical benchmark, for shape comparison).

## Output contract

A JSON object matching `CheckResult` from
`src/vero/curation/validation/types.py`:

```json
{
  "name": "<check_name>",
  "status": "pass | warn | fail",
  "details": [
    {"severity": "info|warn|error", "message": "...", "location": "file:line | null"}
  ]
}
```

Emit the JSON as a fenced ```json code block at the end of the reply.
Text before the block is allowed (and helpful for debugging).

Rule of thumb for severity:
- `info` — positive signal, no action needed.
- `warn` — minor issue; pipeline should continue but the curator should
  look.
- `error` — must be fixed before the benchmark is usable.

Overall status rolls up from severities: any `error` → `fail`, any
`warn` → `warn`, else `pass`.

## Prior Memory

If the request includes `memory_excerpt`, read it before judging. Treat
it as reviewed lessons from prior audits, not as proof that the current
repo has the same problem. Use it to look for recurring patterns and to
avoid repeating known mistakes.

When producing `repo_issue_taxonomy`, prefer lessons that can later be
promoted into deterministic validation rules or stable judge prompts.

## The checks

### `spec_intent_alignment`

**Claim to verify:** every `def spec_* (impl : RepoImpl) : Prop := …`
in `<Project>/Spec/*.lean` correctly formalizes the English intent in
its `/-- … -/` docstring (or in the `plan.json` `nl_description`).

**How to run:**
1. Read `plan.json` if present (for authoritative NL descriptions); else
   fall back to each spec's `/-- -/` docstring.
2. For each spec, compare the natural-language description to the Lean
   body. Ask: "If the Lean body is true, does the English claim hold?
   And vice versa?"
3. Flag:
   - `error` — body contradicts the NL description.
   - `warn` — body misses a case the NL description implies.
   - `info` — matches cleanly.

### `idiom`

**Claim to verify:** the Impl / Harness / Bundle code is idiomatic
Lean 4 and matches the paradigm shape.

**How to run:**
1. Compare the Impl file structure against
   `reference/BankLedger/BankLedger/Impl/*.lean`: types in the
   foundation file, sig abbrevs in `namespace <API>`, and `def
   <API>.<fn> : <API>.<FnSig> := <reference impl>` inside `code`
   markers. Remember that pre-agent generation replaces those bodies
   with `sorry`; the curated source should not contain `sorry` there.
2. Check `<Project>/Bundle.lean`: `structure <Project>Bundle where`
   with one field per API sig. Field names match the API's Lean name
   (camelCase).
3. Check `<Project>/Harness.lean`: `structure RepoImpl where <pkg> :
   <Project>Bundle`; `canonical` wires via `{ <pkg> := { … } }`.
   `joint_unsat` macro present; no other macros.
4. Flag un-idiomatic patterns: mutable state hacks,
   `#[verifier::external_body]`-shaped things, heavy meta-programming
   where a plain `def` would do.

### `test_meaningfulness`

**Claim to verify:** `<Project>/Test.lean`'s `#guard` assertions probe
real behavior (not trivially `True`), cover the API surface, and
include boundary cases.

**How to run:**
1. List every `#guard` in `Test.lean`.
2. For each guard, determine what behavior it exercises. Trivial
   guards (e.g. `#guard True`, `#guard 1 == 1`, `#guard []`) are
   `error`.
3. Check API coverage: does every API in `manifest.json.packages[0].modules[].apis[]`
   have at least one guard touching it? Missing coverage is `warn`.
4. Check boundary cases: empty inputs, duplicate IDs, zero balances,
   missing-account paths. Absence of any boundary case is `warn`.

### `review_annotations`

**Claim to verify:** `!curation @review v1` annotations in `Impl/*`
have sensible content (real concerns, not stale copy-paste).

**How to run:**
1. Grep `!curation @review` across `<Project>/Impl/*.lean`.
2. For each line, check the `<name>` field matches a surrounding
   definition (within ~5 lines).
3. Check the `<notes>` field is non-empty and specific. Generic
   templates ("TODO", "review this") are `warn`.
4. Check the checkbox status (`[ ]` vs `[x]`) — if every annotation
   is `[ ]` (never reviewed), flag `info`; if mixed or fully `[x]`,
   pass.

### `spec_completeness`

**Claim to verify:** the per-module spec set in
`<Project>/Spec/*.lean` covers the API's observable behavior.

**How to run:**
1. For each module, list APIs (from `manifest.json`) and specs.
2. For each API, identify which specs reference it (by name). If any
   API has zero specs, flag `warn`.
3. Check for suspicious absences: e.g., a stateful API that creates
   new data but no spec asserts the data appears; a partial function
   with no spec for the failure path.
4. Don't demand completeness — just flag obvious holes.

### `repo_issue_taxonomy`

**Claim to verify:** the repo's quality issues can be summarized into a
small, reusable taxonomy for future curation/validation.

**How to run:**
1. Read the deterministic validation findings, manifest, source-map /
   plan artifacts if present, and representative Impl/Spec/Test files.
2. Identify recurring patterns, not one-off typos. Examples:
   source contract drift, dropped invariants, vacuous specs, parser
   stubs, manifest/spec mismatch, over-broad trusted axioms, tests that
   cover constants but not APIs.
3. For each pattern, cite evidence with source/Lean paths where possible.
4. Suggest whether the pattern should become:
   - deterministic rule,
   - LLM judge prompt lesson,
   - human review checklist item,
   - repo-local retranslation task.

Use `warn` for actionable quality patterns and `error` only when the
pattern makes the benchmark unusable without correction.

### `trusted_boundary`

**Claim to verify:** trusted, opaque, axiom, and external-runtime
boundaries are explicit, minimal, and do not hide scored benchmark
behavior.

**How to run:**
1. Inspect `manifest.json`, `.vero/plan.json` if present, `Impl/*`,
   `Bundle.lean`, `Harness.lean`, representative `Spec/*`, and `Test.lean`.
2. List every trusted or opaque item: `opaque`, manifest
   `trusted_axioms`, trusted-external plan entries, external-runtime
   wrappers, and any trusted theorem or axiom-like declaration.
3. Check that trusted items are not manifest-scored APIs or Bundle fields
   unless the plan explicitly justifies that boundary.
4. Check that specs mention the trusted boundary concretely rather than
   becoming self-referential, vacuous, or independent of observable API
   behavior.
5. Check that tests do not fake an external result merely to get a
   `#guard`; a `#check`-only API should be reported as a warning unless
   a trusted-boundary testing policy explains why it is acceptable.

Flag:
- `error` — a trusted declaration silently replaces scored behavior,
  appears as a manifest-scored API without review, or introduces an
  unreviewed benchmark-specific axiom/sorry.
- `warn` — the boundary is explicit but promotion-quality questions
  remain, such as non-executable callbacks, missing behavior tests,
  over-broad opaque context, or unclear manifest/bundle metadata.
- `info` — the boundary is explicit, minimal, and reflected in specs and
  tests.

## Tone

Be concrete and specific. "spec_withdraw_insufficient's body says
`amount > bal`, NL says `insufficient funds` — matches." Not "looks
good".

Prefer file:line citations in findings (`location` field).

Keep each check under 15 findings — less is more. If every finding is
`info`, collapse to a single summary finding.
