-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BooleanAlgebra.Impl.NorGate

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BooleanAlgebra

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev NorGateSig := Int → Int → Int
abbrev TruthTableSig := (Int → Int → Int) → String

end BooleanAlgebra

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=nor_gate
-- !benchmark @end code_aux def=nor_gate

def BooleanAlgebra.nor_gate : BooleanAlgebra.NorGateSig :=
-- !benchmark @start code def=nor_gate
  fun a b => if a = 0 ∧ b = 0 then 1 else 0
-- !benchmark @end code def=nor_gate

-- !benchmark @start code_aux def=truth_table
/-- Center-pad an item's textual form to width 8 (Python's `^8` rule:
    extra space on the right when the gap is odd). -/
private def BooleanAlgebra.centerPad8 (s : String) : String :=
  let n := s.length
  if n ≥ 8 then s
  else
    let pad := 8 - n
    let left := pad / 2
    let right := pad - left
    "".pushn ' ' left ++ s ++ "".pushn ' ' right

private def BooleanAlgebra.truthTableRow (items : List String) : String :=
  let centered := items.map BooleanAlgebra.centerPad8
  "| " ++ String.intercalate " | " centered ++ " |"
-- !benchmark @end code_aux def=truth_table

def BooleanAlgebra.truth_table : BooleanAlgebra.TruthTableSig :=
-- !benchmark @start code def=truth_table
  fun f =>
    let header := BooleanAlgebra.truthTableRow ["Input 1", "Input 2", "Output"]
    let mkRow (i j : Int) : String :=
      BooleanAlgebra.truthTableRow [toString i, toString j, toString (f i j)]
    String.intercalate "\n"
      [ "Truth Table of NOR Gate:"
      , header
      , mkRow 0 0
      , mkRow 0 1
      , mkRow 1 0
      , mkRow 1 1 ]
-- !benchmark @end code def=truth_table
