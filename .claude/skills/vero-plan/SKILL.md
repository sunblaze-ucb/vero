---
name: vero-plan
description: Use after vero-select to write a detailed translation plan as `.vero/plan.json` — the authoritative contract the TRANSLATE stage executes. Captures api_namespace, packages, modules, types, APIs (with sig abbrevs + types), specs (with NL descriptions), ref impls, and test cases. Pair with `vero-source-{dafny,verus,coq}`.
allowed-tools: Read, Write, Bash, Grep, Glob
---

# VCG Plan: Emit `plan.json`

Write a detailed translation plan as **JSON**, pinning every Lean
signature the TRANSLATE stage will emit. The plan is reviewed by a
human before translate executes.

**This stage does NOT write any Lean code.** It writes
`.vero/plan.json` (authoritative machine-readable contract) and
`.vero/plan/questions.md` (human-facing questions, if any).

**Canonical example:** `reference/BankLedger/manifest.json` +
`reference/BankLedger/` — the manifest is what translate *produces*;
this stage produces the richer `plan.json` that translate *consumes*
to produce it.

## When to use

- After `.vero/select.json` is approved by the human.
- Before the TRANSLATE stage runs.

## Inputs

| File | Description |
|---|---|
| `.vero/select.json` | Approved selection with proposed packages + module grouping |
| `.vero/discover.json` | Entity catalog (for signatures + doc strings) |
| `.vero/config.json` (or `config.yaml`) | project_name, benchmark_id, lean_version |
| Source code files | To look up exact signatures, `ensures` clauses, test values |

## Output: `.vero/plan.json`

Full schema: `docs/pipeline-schema.md` (`plan.json` section). Minimum
required structure:

```json
{
  "version": 1,
  "api_namespace": "Bank",
  "packages": [
    {
      "name": "BankLedger",
      "is_root": true,
      "bundle_type": "BankLedgerBundle",
      "repo_impl_field": "bankLedger",
      "modules": [
        {
          "name": "Account",
          "upstream_files": ["src/account.rs"],
          "types": [
            {
              "name": "AccountId",
              "lean_form": "abbrev AccountId := Nat",
              "is_foundation": true
            }
          ],
          "apis": [
            {
              "upstream_name": "create_account",
              "lean_name": "createAccount",
              "sig_abbrev": "CreateAccountSig",
              "lean_type": "AccountId → Ledger → Ledger",
              "opaque": false,
              "nl_description": "Add a new account with the given id to the ledger."
            }
          ],
          "spec_helpers": [
            {
              "name": "toSeq",
              "lean_name": "toSeq",
              "lean_form": "def toSeq : Ledger → List (AccountId × Balance)\n  | []            => []\n  | a :: rest     => (a.id, a.balance) :: toSeq rest",
              "nl_description": "Flatten a ledger to a list of (id, balance) pairs; used by specs to state list-level properties."
            }
          ],
          "specs": [
            {
              "name": "spec_create_zero_balance",
              "nl_description": "Creating a new account gives it zero balance.",
              "lean_form": "∀ (id : AccountId) (ledger : Ledger), impl.bankLedger.accountExists id ledger = false → impl.bankLedger.getBalance id (impl.bankLedger.createAccount id ledger) = some 0",
              "apis_referenced": ["createAccount", "accountExists", "getBalance"],
              "spec_helpers_referenced": [],
              "curator_intended_truth": "prove"
            }
          ]
        }
      ]
    }
  ],
  "test_cases": [
    {
      "name": "guard_create_zero_balance",
      "nl_description": "After creating an account it has balance 0.",
      "lean_form": "#guard getBalance 1 (createAccount 1 []) == some 0"
    }
  ]
}
```

**Category mapping from `select.json`:**

| `select.json` category | `plan.json` location |
|---|---|
| `type` | `packages[].modules[].types[]` |
| `api` | `packages[].modules[].apis[]` (sig + reference implementation slot + Bundle field) |
| `api_helper` | Typically absent from plan.json. If the curator *wants* to pre-provide a helper, add it as `packages[].modules[].api_helpers[]` (same shape as `spec_helpers[]`, no Bundle entry), but it must still be backed by a real upstream source item. Do not invent helpers. |
| `spec_helper` | `packages[].modules[].spec_helpers[]` — each with `lean_form` being the **full definition body** (not just a type). These end up as fully-defined `def`s in `Impl/<Module>.lean` with no markers. |
| `spec` | `packages[].modules[].specs[]` |
| `test` | `test_cases[]` at plan top-level |

### Field-by-field guidance

**Top-level:**
- `version`: always `1` for now.
- `api_namespace`: one Lean namespace for the public API (e.g. `"Bank"`
  for BankLedger). Soft convention; may be `null` for multi-namespace
  projects.
- `packages`: exactly one entry has `is_root: true` — its `name` must
  match `config.project_name`. Multi-package projects add non-root
  entries.

**Per-package:**
- `name`: e.g. `"BankLedger"`. Becomes the package directory name.
- `bundle_type`: PascalCase, typically `"<Name>Bundle"`.
- `repo_impl_field`: lowerCamelCase of `name`, the field inside
  `structure RepoImpl`.

**Per-module:**
- `name`: PascalCase module name (`"Account"`, `"Transaction"`).
- `upstream_files`: list of source files this module consolidates.

**types[]:**
- `name`: Lean type name.
- `lean_form`: full Lean declaration text (the curator inspects this
  verbatim). `"abbrev X := …"`, `"structure X where …"`, or
  `"inductive X where …"`.
- `is_foundation`: `true` if this type must live in the foundation
  Impl file (the one every other Impl imports).
- `source_id`, `source_file`, `source_line`, `upstream_name`, and
  `source_signature`: provenance for the exact upstream declaration.

**apis[]:**
- `upstream_name`: source-side name (`create_account` in Rust).
- `lean_name`: Lean-side name after casing (`createAccount`).
- `sig_abbrev`: PascalCase abbrev, conventionally `<LeanName>Sig` with
  first letter uppercased (`CreateAccountSig`).
- `lean_type`: the type body — exactly what goes after `:=` in
  `abbrev <sig_abbrev> := <type>`. Use Unicode arrows (`→`), not
  ASCII.
- `opaque`: `true` for FFI / external functions — translate emits
  `opaque` + axioms instead of a translated reference implementation slot.
- `nl_description`: one-sentence English summary. Used later by
  `vero-validate` for spec-intent alignment.
- `source_id`, `source_file`, `source_line`, and `source_signature`:
  provenance for the exact upstream declaration.

**specs[]:**
- `name`: must start with `spec_`.
- `nl_description`: one-sentence English summary of what the spec
  asserts.
- `lean_form`: the body of `def spec_<…> (impl : RepoImpl) : Prop := …`.
  Access APIs via `impl.<repo_impl_field>.<lean_name>` — never bare
  `impl.<lean_name>` (RepoImpl is one-level-nested).
- `apis_referenced`: list of `lean_name`s the spec touches. Helps the
  validator's `spec_completeness` check.
- `curator_intended_truth`: `"prove" | "disprove" | "unsat" | "sat" | "unknown"`.
  Curator's ground-truth label for coverage scoring; may be
  `"unknown"` if undecided.
- `source_id`, `source_file`, `source_line`, `source_theorem`, and
  `source_signature`: provenance for the exact upstream theorem/lemma.

**Source-provenance rule (hard requirement).** Every translated plan
item in `types[]`, `apis[]`, `api_helpers[]`, `spec_helpers[]`,
`specs[]`, and `ref_impls[]` must be backed by a real upstream source
item. Prefer the exact `source_id` from `.vero/source_index.json`;
also carry `source_file`, `source_line`, and the source signature when
available. Do not create generated source ids, blank source files,
sentinel predicates, token wrappers, placeholder helpers, or review
marker definitions to preserve an item whose Lean translation is not
known. If a selected item cannot be faithfully translated now, do not
emit it as a translated/scored item; move it to review-only/untranslated
metadata with a reason.

**Disposition vocabulary (hard requirement).** Use only
`unclassified`, `provided`, `scored`, `hidden`, `dropped`,
`axiomatized`, or `opaque`. Use `provided` for fixed source-backed
vocabulary that is translated and supplied to the benchmark, such as
types and spec helpers. Do not write `given`; it is a deprecated synonym
and will be normalized or rejected by validation.

`requires_human_review` and `equivalence_status: "unclear"` are not
allowed inside translated/scored item lists. They mean the item is not
ready to translate. Keep such items out of `types[]`, `apis[]`,
`api_helpers[]`, `spec_helpers[]`, and `specs[]` until a faithful Lean
form is available.

**Reference implementations (no separate field).** The reference
implementation of each non-opaque API is written directly inside the
`code` marker in `Impl/<Module>.lean` by the TRANSLATE stage — not in
a separate `Bank.Ref` namespace, not in a `ref_impls[]` plan field.
Pre-agent-gen replaces marker content with `sorry` before the LLM sees
the benchmark. This keeps one source of truth and lets `#guard` tests
hit real code at curation / build time.

**test_cases[]:** `#guard` assertions against `Bank.*` directly. Each
with an English description and the Lean form. Prefer boundary cases
(empty inputs, duplicates, partial-function failure paths).

## Output: `.vero/plan/questions.md` (optional)

If any decision is genuinely ambiguous (the source doesn't commit to a
shape), write a bulleted list of questions for the human:

```markdown
## Questions

- `pop` — source uses `requires s.nonEmpty`. Map to `Option (Stack α)` or
  `(s : Stack α) → s.size > 0 → Stack α`? Recommendation: `Option`
  (simpler, works with `#guard`).
```

The human answers inline by editing the file; re-run vero-plan on
resume to pick up the answers.

## How to run (incremental — module by module)

Plan the repo one module at a time. The final `plan.json` is built up
by appending a complete module entry each pass, so partial progress
is observable and the run is restartable.

1. Read config for `project_name`, `benchmark_id`, `lean_version`.
2. Read `.vero/select.json` — walk `proposed_packages[].modules[]`.
3. Also read `.vero/discover.json` — lets you look up items by
   qualified name without re-reading source.
4. Also read `.vero/source_index.json` — every translated item must
   resolve to one of these source entities.
5. **Scaffold the JSON first.** Write `.vero/plan.json` with the
   top-level fields filled in (`version`, `api_namespace`, `packages`
   with empty `modules: []`), plus an empty `test_cases: []`. This
   is a valid JSON anchor to Edit into.
6. **For each module in `select.json` (one at a time, not batched):**
   a. Read ONLY the upstream source files for that module's selected
      entities (typically 1–3 files). Do not read files for other
      modules yet.
   b. Work out this module's `types[]`, `apis[]`, `specs[]` per the
      field guidance above. Use `vero-source-<lang>` for type
      mappings.
   c. `Edit` `plan.json` to append this module's fully-specified
      entry to the enclosing package's `modules[]`. Keep the JSON
      valid after every edit (parse it back with a one-line Bash
      `python -c "import json; json.load(open('…'))"` as a
      lightweight check).
   d. Announce before and after: "Planning module `Merkle` (3
      types, 5 APIs, 12 specs)." ... "Merkle appended. Moving on to
      `Contract`."
7. After all modules are done, `Edit` `plan.json` to populate
   `test_cases[]` — emit them in small groups, grouped by the
   primary API they exercise.
8. If any decision is ambiguous, Write `.vero/plan/questions.md`
   with a bulleted list. Do this at the end so the file tracks every
   open question in one place.
9. No `ref_impls` field — the reference implementation is the body
   the TRANSLATE stage writes inside each API's `code` marker
   directly.

**Do not** compose the whole `plan.json` as one giant string and
then `Write` it once. That is the failure mode that loses everything
on interrupt.

## Quality bar

- Every `category=api` item in `select.json` appears in exactly one module's `apis[]`.
- Every `category=spec` item appears in exactly one module's `specs[]`.
- Every `category=spec_helper` item appears in exactly one module's `spec_helpers[]` with a full `lean_form` definition body.
- Every `category=type` item appears in exactly one module's `types[]`.
- Every translated item has source provenance resolving to
  `.vero/source_index.json`. Any generated, placeholder, blank, or
  unresolved source provenance is a plan-stage failure.
- No translated item is marked `requires_human_review`; no translated
  spec has `equivalence_status: "unclear"`. These must be
  review-only/untranslated, not benchmark specs.
- Spec `lean_form` bodies use `impl.<pkg>.<fn>` for API references and bare names for spec-helper / type / stdlib references — never bare for an API, never `impl.<…>` for a spec helper.
- **Spec name-resolution check.** For every `specs[].lean_form` body, every bare identifier it mentions (other than Lean keywords, lambda binders, and stdlib) must resolve to a `types[]`, `spec_helpers[]`, or `api_helpers[]` entry in the same or a dependency module. Every `impl.<pkg>.<name>` reference must resolve to an `apis[]` entry. A reference that doesn't resolve is a hard error — fail the plan stage with a clear message and a pointer to which spec is broken.
- Each `sig_abbrev` is unique across the project.
- The foundation module's `types[]` cover everything the other modules need to import.
- No two modules declare the same type name (types live in exactly one Impl file).
- `spec_helpers[].name` is unique across the project (one definition per helper).

## Non-goals

- **No Lean code in `plan.json`** beyond `lean_form` strings. This is
  planning, not translation.
- **No proof bodies.** The proofs are materialized downstream.
- **No marker placement.** `!benchmark` markers are emitted by
  TRANSLATE; the plan only names the slots that will exist.
- **No `Proof/`** — proof files are NOT a curation artifact.

## Pair with

- `vero-source-{dafny,verus,coq}` — per-language type mappings and
  classification rules.
- `vero-translate` — consumes this plan.
- `vero-validate` — checks the translated output against this plan
  during the validate stage.
