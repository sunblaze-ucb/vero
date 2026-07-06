import Huffman.Bundle

/-!
# Huffman.Harness

Benchmark harness: `RepoImpl`, canonical implementation wiring, and `joint_unsat`.

DO NOT MODIFY - benchmark infrastructure.
-/

structure RepoImpl where
  huffman : HuffmanBundle

noncomputable def canonical : RepoImpl where
  huffman := {
    all_leaves            := Huffman.all_leaves
    compute_code          := Huffman.compute_code
    find_code             := Huffman.find_code
    find_val              := Huffman.find_val
    decode                := Huffman.decode
    encode                := Huffman.encode
    all_pbleaves          := Huffman.all_pbleaves
    compute_pbcode        := Huffman.compute_pbcode
    pbadd                 := Huffman.pbadd
    pbbuild               := Huffman.pbbuild
    build_fun             := Huffman.build_fun
    buildf                := Huffman.buildf
    obuildf               := Huffman.obuildf
    add_frequency_list    := Huffman.add_frequency_list
    frequency_list        := Huffman.frequency_list
    number_of_occurrences := Huffman.number_of_occurrences
    sum_leaves            := Huffman.sum_leaves
    weight_tree           := Huffman.weight_tree
    weight_tree_list      := Huffman.weight_tree_list
    insert                := Huffman.insert
    isort                 := Huffman.isort
    to_btree              := Huffman.to_btree
    prod2list             := Huffman.prod2list
    restrict_code         := Huffman.restrict_code
    weight_restrict_code  := Huffman.weight_restrict_code
    weight                := Huffman.weight
    huffman               := Huffman.huffman
  }

/--
`joint_unsat spec_A spec_B [spec_C ...] by <proof>` generates
a theorem showing no implementation can satisfy all listed specs.
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
