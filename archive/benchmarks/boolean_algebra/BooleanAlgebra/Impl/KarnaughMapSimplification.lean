-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BooleanAlgebra.Impl.KarnaughMapSimplification

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BooleanAlgebra

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev SimplifyKmapSig := List (List Int) → String

end BooleanAlgebra

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=simplify_kmap
-- !benchmark @end code_aux def=simplify_kmap

def BooleanAlgebra.simplify_kmap : BooleanAlgebra.SimplifyKmapSig :=
-- !benchmark @start code def=simplify_kmap
  fun kmap =>
    let terms : List String :=
      (kmap.zipIdx).foldl (init := []) fun acc (row, a) =>
        let rowTerms : List String :=
          (row.zipIdx).foldl (init := []) fun innerAcc (item, b) =>
            if item ≠ 0 then
              let aPart := if a ≠ 0 then "A" else "A'"
              let bPart := if b ≠ 0 then "B" else "B'"
              innerAcc ++ [aPart ++ bPart]
            else innerAcc
        acc ++ rowTerms
    String.intercalate " + " terms
-- !benchmark @end code def=simplify_kmap
