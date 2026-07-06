import UnicodeV2.Bundle

/-!
# Unicode.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring, and the `joint_unsat` macro consumed by
`codeproof`-mode `Proof/Joint.lean`.

DO NOT MODIFY this file. This is the benchmark infrastructure.

`RepoImpl` is uniformly a `structure` with one field per package (each
field typed as `<Package>Bundle`). Single-package benchmarks (this one)
have exactly one field. Specs always access API functions via
`impl.unicodeV2.<fn>`, making the shape the same across cases.

Per-module proof stubs use direct theorem statements — no macros.
Only `joint_unsat` needs a macro (variadic arity). Specs appear in the
caller's order; no sort / no dedup — anti-cheat is enforced at
`!solution` extraction during evaluation.
-/

-- ── Implementation bundle (one field per package) ────────────────────

structure RepoImpl where
  unicodeV2 : UnicodeV2Bundle

-- ── Canonical instance ───────────────────────────────────────────────
-- Instantiates each API in the bundle with the curator's reference
-- implementation from the corresponding `Impl/` file.
-- In `proof` mode, `canonical` is given. In `codeproof` mode,
-- `canonical` points at LLM-filled `Unicode.*` defs.

def canonical : RepoImpl where
  unicodeV2 := {
    uefIsMinimalWellFormedCodeUnitSubsequence      := Unicode.uefIsMinimalWellFormedCodeUnitSubsequence
    uefSplitPrefixMinimalWellFormedCodeUnitSubsequence := Unicode.uefSplitPrefixMinimalWellFormedCodeUnitSubsequence
    uefEncodeScalarValue                           := Unicode.uefEncodeScalarValue
    uefDecodeMinimalWellFormedCodeUnitSubsequence  := Unicode.uefDecodeMinimalWellFormedCodeUnitSubsequence
    uefPartitionCodeUnitSequenceChecked            := Unicode.uefPartitionCodeUnitSequenceChecked
    uefPartitionCodeUnitSequence                   := Unicode.uefPartitionCodeUnitSequence
    uefEncodeScalarSequence                        := Unicode.uefEncodeScalarSequence
    uefDecodeCodeUnitSequence                      := Unicode.uefDecodeCodeUnitSequence
    uefDecodeCodeUnitSequenceChecked               := Unicode.uefDecodeCodeUnitSequenceChecked
    absToUTF8Checked                               := Unicode.absToUTF8Checked
    absASCIIToUTF8                                 := Unicode.absASCIIToUTF8
    absFromUTF8Checked                             := Unicode.absFromUTF8Checked
    absToUTF16Checked                              := Unicode.absToUTF16Checked
    absASCIIToUTF16                                := Unicode.absASCIIToUTF16
    absFromUTF16Checked                            := Unicode.absFromUTF16Checked
    utf8IsMinimalWellFormedCodeUnitSubsequence     := Unicode.utf8IsMinimalWellFormedCodeUnitSubsequence
    utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence := Unicode.utf8SplitPrefixMinimalWellFormedCodeUnitSubsequence
    utf8EncodeScalarValue                          := Unicode.utf8EncodeScalarValue
    utf8DecodeMinimalWellFormedCodeUnitSubsequence := Unicode.utf8DecodeMinimalWellFormedCodeUnitSubsequence
    utf16IsMinimalWellFormedCodeUnitSubsequence     := Unicode.utf16IsMinimalWellFormedCodeUnitSubsequence
    utf16SplitPrefixMinimalWellFormedCodeUnitSubsequence := Unicode.utf16SplitPrefixMinimalWellFormedCodeUnitSubsequence
    utf16EncodeScalarValue                          := Unicode.utf16EncodeScalarValue
    utf16DecodeMinimalWellFormedCodeUnitSubsequence := Unicode.utf16DecodeMinimalWellFormedCodeUnitSubsequence
    serialize                                      := Unicode.serialize
    deserialize                                    := Unicode.deserialize
    noCharToUTF8Checked                            := Unicode.noCharToUTF8Checked
    noCharFromUTF8Checked                          := Unicode.noCharFromUTF8Checked
    noCharToUTF16Checked                           := Unicode.noCharToUTF16Checked
    noCharFromUTF16Checked                         := Unicode.noCharFromUTF16Checked
    uniCharToUTF8Checked                           := Unicode.uniCharToUTF8Checked
    uniCharFromUTF8Checked                         := Unicode.uniCharFromUTF8Checked
    uniCharToUTF16Checked                          := Unicode.uniCharToUTF16Checked
    uniCharFromUTF16Checked                        := Unicode.uniCharFromUTF16Checked
  }

-- ── joint_unsat macro ────────────────────────────────────────────────

/--
`joint_unsat spec_A spec_B [spec_C …] by <proof>` generates
```
theorem joint_unsat.spec_A.spec_B.… :
    ¬ ∃ impl : RepoImpl, spec_A impl ∧ spec_B impl ∧ … := by <proof>
```

Specs appear in the caller's order. No sorting, no deduplication —
anti-cheat for joint-unsat claims is enforced at evaluation by
extracting the spec list from the companion `!solution` marker
(rejecting duplicates there) and rerendering this macro from the
extracted list.
-/
syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
