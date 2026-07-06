import Compression.Bundle

/-!
# Compression.Harness

Benchmark harness: `RepoImpl` structure (one field per package),
`canonical` instance wiring, and the `joint_unsat` macro.

DO NOT MODIFY — benchmark infrastructure.
-/

/-- Single-field repo implementation: the `Compression` package bundle. -/
structure RepoImpl where
  compression : CompressionBundle

/-- Canonical wiring that connects every API stub to the reference
    implementations from `Compression.Impl.*`. -/
def canonical : RepoImpl where
  compression := {
    traverse_tree     := Compression.traverse_tree
    build_tree        := Compression.build_tree
    all_rotations     := Compression.all_rotations
    bwt_transform     := Compression.bwt_transform
    reverse_bwt       := Compression.reverse_bwt
    lz77Compress      := Compression.LZ77Compressor.compress
    lz77Decompress    := Compression.LZ77Compressor.decompress
    run_length_encode := Compression.run_length_encode
    run_length_decode := Compression.run_length_decode
    coordDecompress   := @Compression.CoordinateCompressor.decompress
    coordCompress     := @Compression.CoordinateCompressor.compress
  }

/-- `joint_unsat spec_A spec_B [spec_C …] by <proof>` generates the
    ∧-conjunction unsat theorem. Variadic; no sort / no dedup — anti-cheat
    is enforced at `!solution` extraction during evaluation. -/
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
