# Vero: A benchmark for repository-level verified code generation in Lean 4.

AI agents are increasingly used for programming, but they give no guarantee about the correctness of the code they produce. Verified code generation, in which an agent produces both an implementation and a machine-checked proof that it satisfies its specification, offers a stronger path toward trustworthy AI-generated software. Existing benchmarks in this direction either focus on individual functions or only evaluate proof generation against a provided implementation, so whether agents can make coherent implementation and proof choices across real multi-module codebases remains an open question.

Vero is the first benchmark to evaluate joint implementation and proof synthesis at the repository level. It contains 43 instances sourced from real-world repositories spanning Python, Dafny, Verus, and Coq, covering domains from cryptographic protocols to distributed systems. Each instance is a Lean 4 repository with predetermined API interfaces, manually curated formal specifications, and reference implementations, and it supports both proof-only and code-and-proof evaluation modes. Because every instance is translated into Lean 4 with manual validation, no Lean 4 ground-truth solution exists online, which is a structural guard against training-data contamination. Vero also includes an audit mechanism in which agents can formally prove that a provided specification is unsatisfiable or that reference code is incorrect, surfacing and correcting latent code and specification errors during curation. The full benchmark list is in the [benchmark inventory](#benchmark-inventory).

## What a benchmark instance looks like

A benchmark is a self-contained multi-module Lean 4 project. The curator provides three frozen layers (shared data types and helpers, API signatures, and formal specifications), and the agent discharges two kinds of obligation. It writes an implementation for each API and a proof for each spec. The glue is a single interface structure, with specs written against it.

```lean
-- API signatures (frozen)
abbrev CreateAccountSig := AccountId → Ledger → Ledger
abbrev AccountExistsSig := AccountId → Ledger → Bool
abbrev GetBalanceSig    := AccountId → Ledger → Option Balance

-- One field per API (frozen)
structure RepoImpl where
  createAccount : CreateAccountSig
  accountExists : AccountExistsSig
  getBalance    : GetBalanceSig

-- A spec is a predicate over *any* implementation (frozen)
def spec_create_zero_balance (impl : RepoImpl) : Prop :=
  ∀ id ledger, impl.accountExists id ledger = false →
    impl.getBalance id (impl.createAccount id ledger) = some 0

-- `canonical` is the reference impl in proof mode, or the agent's own impl
-- in codeproof mode. The agent's obligation is to discharge the proof.
theorem proof_create_zero_balance : spec_create_zero_balance canonical := by
  sorry   -- ← agent fills this
```

Because each spec is parameterized over `RepoImpl` rather than one fixed implementation, the same benchmark drives both evaluation modes and the audit mechanism described below.

The full `bankledger` instance under [`reference/BankLedger/`](reference/BankLedger) is the canonical exemplar and the best starting point for understanding the project. Its [`ARCHITECTURE.md`](reference/BankLedger/ARCHITECTURE.md) walks through every file, and `vero run benchmark=bankledger agent=claude mode=proof` runs it end to end.

## Two evaluation modes

- **`proof`** supplies the reference implementation, and the agent must prove every spec against it. For each spec `S`, exactly one of `prove_S : spec_S canonical` or `disprove_S : ¬ spec_S canonical` is filled, and it must be axiom-clean.
- **`codeproof`** withholds the reference implementation (its bodies are `sorry`), and the agent writes both the implementations and the proofs. For each spec, exactly one of `prove_S`, `unsat_S` (`¬ ∃ impl, spec_S impl`), or `sat_S` (paired with a verified `joint_unsat` claim).

Full coverage matters, because any unproven spec leaves room for the bug it would have caught.

**Audit mechanism.** The `disprove_`, `unsat_`, and `joint_unsat` slots let an agent submit machine-checked negative evidence. It can show that the reference implementation violates a spec, that a spec is individually unsatisfiable, or that a set of specs is mutually inconsistent. This turns latent curation errors into formal, actionable findings instead of silent agent failures, and it keeps the benchmark improvable as agents get stronger. The `tiny_unsat` benchmark is a minimal, self-contained example of these paths, and `vero run benchmark=tiny_unsat mode=codeproof` exercises the `unsat_` and `joint_unsat` audit flow end to end.

**Anti-cheat.** Grading never trusts the agent's own project. The grader re-renders a fresh Lean project from the source benchmark and overlays only the agent's marker-slot bodies, then compiles with Lake and checks each proof's axioms against an allowlist. A proof that leaks `sorry` or an injected axiom does not count. A rule-based and LLM-judge screen also rejects trivializing typeclass instances. Editing a frozen file, or renaming and adding markers, cannot change the score.

## Quickstart

vero needs Python 3.10 or newer, [`uv`](https://github.com/astral-sh/uv), and a Lean 4 toolchain. Benchmarks pin Lean v4.29.1, and [`elan`](https://github.com/leanprover/elan) installs it on the first `lake build`. A few benchmarks depend on mathlib, and most are mathlib-free.

```bash
uv sync && source .venv/bin/activate
cp .env.example .env        # add the API key for your agent (see docs/agents.md)

# proof mode, Claude agent, on the BankLedger exemplar
vero run benchmark=bankledger agent=claude mode=proof

# codeproof mode, Codex agent
vero run benchmark=bankledger agent=codex mode=codeproof

# re-grade an existing run without regenerating
vero run run=<run-name> eval.name=retry
```

Results land in `agent_runs/<run>/eval/<name>/report.md`, with per-spec status and an axiom breakdown. The full walkthrough is [`docs/gen-eval-tutorial.md`](docs/gen-eval-tutorial.md).

## Bring your own agent

vero owns the harness, and the agent is a small, swappable part. For each run vero renders a sandbox, which is a fresh Lean project with the fill-in slots marked (`!benchmark @start … @end`) and an `INSTRUCTION.md`. The agent's only job is to edit those slot bodies in place, using whatever Lean tooling it likes (`lake build`, an LSP, search). vero then extracts what the agent wrote, re-renders a clean anti-cheat sandbox, and scores it. The agent never parses the benchmark format and never calls render, extract, or grade.

Integrating one takes roughly fifteen lines. You implement a single `_run_inner(sandbox_dir, instruction_file)` method that launches your agent against the directory. A fully-decoupled path (render, edit, then grade, with no vero code) also works. See [`docs/agents.md`](docs/agents.md).

## Documentation

| Doc | What it covers |
|---|---|
| [`docs/gen-eval-tutorial.md`](docs/gen-eval-tutorial.md) | How to run generation and evaluation. Covers the `vero run` command, modes, output layout, re-eval, sweeps, and the iteration harness. |
| [`docs/agents.md`](docs/agents.md) | Credential setup, the built-in agents, and how to plug in your own agent. |
| [`docs/pipeline-schema.md`](docs/pipeline-schema.md) | Authoritative JSON schemas for every artifact (`manifest.json`, `artifact.json`, and more). |
| [`docs/curation-lean-tutorial.md`](docs/curation-lean-tutorial.md) | Curating a Lean-source repository into a benchmark. |
| [`src/vero/curation/README.md`](src/vero/curation/README.md) | The curation pipeline internals, including stages, CLI, and skills. |
| [`reference/BankLedger/`](reference/BankLedger) | The canonical exemplar instance, the living contract. |

## Curation (extending the benchmark)

New instances are built by a semi-automated, multi-stage pipeline (`discover → select → plan → translate → [spec_write] → validate`), where each stage runs as an LLM agent behind a human-review gate. There are two tracks. Formal sources (Dafny, Verus, Coq) are translated, reusing their existing specifications. Non-formal sources (Python) are translated and given hand-written specifications. Adding a source language is a matter of writing a new skill under `.claude/skills/vero-source-*`.

```bash
python -m vero.curation …   # see src/vero/curation/README.md
```

## Repository layout

```
benchmarks/   the curated benchmark projects (one Lean project each)
conf/         Hydra configs for conf/{benchmark,agent,credentials}/*.yaml
reference/    BankLedger, the canonical exemplar / living contract
src/vero/     the pipeline (curation, generation agents, evaluation grader)
docs/         tutorials and schema reference
templates/    Jinja templates for agent instructions and rendered files
tests/        pytest suite
```

## Development

```bash
uv run ruff check
uv run ruff format --check
uv run pytest
```

Contributor conventions live in `CLAUDE.md`. When changing benchmark conventions (markers, manifest shape, `RepoImpl` shape), update `reference/BankLedger/` first, since it is the canonical exemplar that drives the curation tooling and validator.

## License

Vero's own code (the curation, generation, and evaluation pipeline, the harness, and the specifications and scaffolding written for this project) is released under the Apache License 2.0. See [`LICENSE`](LICENSE).

Each benchmark is a hand-written Lean 4 translation of a third-party source repository, and its upstream license is listed in the [benchmark inventory](#benchmark-inventory) below. Benchmarks derived from permissively-licensed upstreams (MIT, BSD, ISC, PSF-2.0, Apache-2.0, and similar) are redistributed here under the project's Apache-2.0 terms with attribution.

Three active benchmarks derive from copyleft upstreams and stay under their upstream license rather than Apache-2.0. Each ships the upstream license file in its own directory.

| Benchmark | License | License file |
|---|---|---|
| `flocq` | LGPL-3.0-or-later | `benchmarks/Flocq/COPYING` |
| `huffman` | LGPL-2.1-or-later | `benchmarks/Huffman/LICENSE` |
| `portion` | LGPL-3.0-or-later | `benchmarks/portion/LICENSE.txt` |

Benchmarks under `archive/benchmarks/` are retained for provenance only and are outside the released suite.

## Benchmark inventory

Every benchmark is a standalone Lean 4 project under `benchmarks/<name>/` (the `bankledger` exemplar lives under `reference/`) with a `manifest.json`, a frozen reference `Impl/`, frozen `Spec/`, and a `Harness.lean` exposing `canonical : RepoImpl`. Each row is a runnable `benchmark=<id>` target. **# API** and **# Spec** are the scored counts from that benchmark's `manifest.json`. **Commit / tag** pins the exact upstream revision the translation was curated against. **License** is the upstream project's license, verified against its published `LICENSE`.

| Benchmark | # API | # Spec | Upstream repo | License | Commit / tag |
|---|--:|--:|---|---|---|
| `arithmetic` | 54 | 191 | [verus-lang/verus](https://github.com/verus-lang/verus.git) | MIT | `8c06fbd72483` |
| `bankledger` | 10 | 11 | *(original exemplar)* | n/a | `n/a` |
| `base58` | 4 | 53 | [keis/base58](https://github.com/keis/base58) | MIT | `2fae7065e344` |
| `cachetools` | 5 | 74 | [tkem/cachetools](https://github.com/tkem/cachetools) | MIT | `48284d73d0a8` |
| `croniter` | 3 | 55 | [kiorky/croniter](https://github.com/kiorky/croniter) | MIT | `9810279c2003` |
| `dedekind_reals` | 17 | 82 | [rocq-community/dedekind-reals](https://github.com/rocq-community/dedekind-reals.git) | MIT | `da4a7452e1d2` |
| `deposit_sc` | 22 | 79 | [ConsenSys/deposit-sc-dafny](https://github.com/ConsenSys/deposit-sc-dafny) | Apache-2.0 | `cf321d10953c` |
| `difflib` | 3 | 49 | [python/cpython](https://github.com/python/cpython) | PSF-2.0 | `669299b62f6c` |
| `dijkstar` | 3 | 43 | [wylee/dijkstar](https://github.com/wylee/dijkstar) | MIT | `aa1237a8de39` |
| `ecdsa` | 9 | 48 | [tlsfuzzer/python-ecdsa](https://github.com/tlsfuzzer/python-ecdsa) | MIT | `bff40c6cf234` |
| `flocq` | 73 | 203 | [flocq/flocq](https://gitlab.inria.fr/flocq/flocq.git) | LGPL-3.0-or-later | `7aab8f55bcee` |
| `galoistools` | 11 | 48 | [sympy/sympy](https://github.com/sympy/sympy) | BSD-3-Clause | `2f9c274d2021` |
| `greenery` | 7 | 26 | [qntm/greenery](https://github.com/qntm/greenery) | MIT | `588f5e3034a6` |
| `huffman` | 27 | 127 | [rocq-community/huffman](https://github.com/rocq-community/huffman.git) | LGPL-2.1-or-later | `cc7d4cc41ef6` |
| `intervaltree` | 3 | 56 | [chaimleib/intervaltree](https://github.com/chaimleib/intervaltree) | Apache-2.0 | `1bc406e1f441` |
| `ipaddress` | 5 | 68 | [python/cpython](https://github.com/python/cpython) | PSF-2.0 | `669299b62f6c` |
| `json` | 31 | 64 | [dafny-lang/libraries](https://github.com/dafny-lang/libraries.git) | MIT | `b486ff7faadb` |
| `jsonpatch` | 5 | 27 | [stefankoegl/python-json-patch](https://github.com/stefankoegl/python-json-patch) | BSD-3-Clause | `0b0520328504` |
| `linked_list` | 64 | 109 | [TheAlgorithms/Python](https://github.com/TheAlgorithms/Python.git) | MIT | `7a0fee401d29` |
| `munkres` | 4 | 19 | [bmc/munkres](https://github.com/bmc/munkres) | Apache-2.0 | `ac8af9e3b609` |
| `netaddr` | 5 | 40 | [netaddr/netaddr](https://github.com/netaddr/netaddr) | BSD-3-Clause | `d340feab548d` |
| `networkx` | 6 | 40 | [networkx/networkx](https://github.com/networkx/networkx) | BSD-3-Clause | `195092869192` |
| `ntheory` | 8 | 62 | [sympy/sympy](https://github.com/sympy/sympy) | BSD-3-Clause | `1a2501b30c1b` |
| `packaging_version` | 5 | 74 | [pypa/packaging](https://github.com/pypa/packaging) | Apache-2.0 OR BSD-2-Clause | `dcac24cc0a37` |
| `piggybank` | 4 | 23 | [AU-COBRA/ConCert](https://github.com/AU-COBRA/ConCert.git) | MIT | `341f440abb95` |
| `portion` | 6 | 63 | [AlexandreDecan/portion](https://github.com/AlexandreDecan/portion) | LGPL-3.0-or-later | `b771acfa2ea1` |
| `primefac` | 3 | 56 | [elliptic-shiho/primefac-fork](https://github.com/elliptic-shiho/primefac-fork) | MIT | `28adf4aa3061` |
| `primepy` | 7 | 9 | [janaindrajit/primePy](https://github.com/janaindrajit/primePy) | MIT | `9c98276fee52` |
| `prolepticgregorian` | 6 | 61 | [python/cpython](https://github.com/python/cpython) | PSF-2.0 | `669299b62f6c` |
| `pyradix` | 6 | 52 | [mjschultz/py-radix](https://github.com/mjschultz/py-radix) | ISC | `b5e4e9303147` |
| `pythonconstraint` | 4 | 20 | [python-constraint/python-constraint](https://github.com/python-constraint/python-constraint) | BSD-2-Clause | `f1359ff0ff6d` |
| `reedsolo` | 5 | 48 | [tomerfiliba-org/reedsolomon](https://github.com/tomerfiliba-org/reedsolomon) | Unlicense OR MIT-0 | `796639ca4953` |
| `rsa` | 6 | 63 | [sybrenstuvel/python-rsa](https://github.com/sybrenstuvel/python-rsa) | Apache-2.0 | `42b0e14ffbee` |
| `semver` | 5 | 53 | [rbarrois/python-semanticversion](https://github.com/rbarrois/python-semanticversion) | BSD-2-Clause | `2cbbee3154d9` |
| `sequences` | 39 | 84 | [dafny-lang/libraries](https://github.com/dafny-lang/libraries.git) | MIT | `b486ff7faadb` |
| `sortedcontainers` | 71 | 49 | [grantjenks/python-sortedcontainers](https://github.com/grantjenks/python-sortedcontainers) | Apache-2.0 | `3ac358631f58` |
| `textdistance` | 2 | 59 | [life4/textdistance](https://github.com/life4/textdistance) | MIT | `d6a68d61088a` |
| `textwrap` | 2 | 60 | [python/cpython](https://github.com/python/cpython) | PSF-2.0 | `669299b62f6c` |
| `toposort` | 2 | 15 | [ericvsmith/toposort](https://gitlab.com/ericvsmith/toposort) | Apache-2.0 | `9fcd043736d3` |
| `unicode` | 30 | 46 | [dafny-lang/libraries](https://github.com/dafny-lang/libraries.git) | MIT | `b486ff7faadb` |
| `verdict` | 31 | 120 | [secure-foundations/verdict](https://github.com/secure-foundations/verdict) | MIT OR Apache-2.0 | `9bc18bc5a287` |
| `verified_bitmasks` | 88 | 124 | [achreto/verified-bitmasks](https://github.com/achreto/verified-bitmasks.git) | MIT | `cce6985c3d99` |
| `verified_ironkv` | 23 | 22 | [verus-lang/verified-ironkv](https://github.com/verus-lang/verified-ironkv.git) | MIT | `08be20c3c356` |
| `vest` | 29 | 42 | [secure-foundations/vest](https://github.com/secure-foundations/vest.git) | MIT | `db63c23b1a63` |

*Totals: 43 benchmark instances, 743 APIs, 2,706 scored specs (plus the BankLedger exemplar).*

### Archived

The instances below live under `archive/benchmarks/` and are **not** part of the active suite. They are older, incomplete, or lower-quality translations, or were already solved by frontier agents, and are kept only for provenance.

| Benchmark | Upstream repo |
|---|---|
| `bidict` | [jab/bidict](https://github.com/jab/bidict) |
| `bit_manipulation` | [TheAlgorithms/Python](https://github.com/TheAlgorithms/Python.git) |
| `bitlist` | [lapets/bitlist](https://github.com/lapets/bitlist) |
| `bmpwriter` | [python-pillow/Pillow](https://github.com/python-pillow/Pillow) |
| `boolean_algebra` | [TheAlgorithms/Python](https://github.com/TheAlgorithms/Python.git) |
| `compression` | [TheAlgorithms/Python](https://github.com/TheAlgorithms/Python.git) |
| `DafnyVmc` | [dafny-lang/Dafny-VMC](https://github.com/dafny-lang/Dafny-VMC) |
| `Dafnycrypto` | [Consensys/DafnyCrypto](https://github.com/Consensys/DafnyCrypto.git) |
| `eip20` | [AU-COBRA/ConCert](https://github.com/AU-COBRA/ConCert.git) |
| `escrow` | [AU-COBRA/ConCert](https://github.com/AU-COBRA/ConCert.git) |
| `Eth20Dafny` | [Consensys/eth2.0-dafny](https://github.com/Consensys/eth2.0-dafny.git) |
| `heap` | [TheAlgorithms/Python](https://github.com/TheAlgorithms/Python.git) |
| `leftpad` | [hwayne/lets-prove-leftpad](https://github.com/hwayne/lets-prove-leftpad) |
| `number_theory` | [TheAlgorithms/Python](https://github.com/TheAlgorithms/Python.git) |
| `pygtrie` | [google/pygtrie](https://github.com/google/pygtrie) |
| `queues` | [TheAlgorithms/Python](https://github.com/TheAlgorithms/Python.git) |
| `special_numbers` | [TheAlgorithms/Python](https://github.com/TheAlgorithms/Python.git) |
| `stack` | [TheAlgorithms/Python](https://github.com/TheAlgorithms/Python.git) |
| `suffix_tree` | [TheAlgorithms/Python](https://github.com/TheAlgorithms/Python.git) |
