-- !benchmark @start imports
-- !benchmark @end imports

/-!
# BooleanAlgebra.Impl.QuineMcCluskey

Scaffolded from `benchmark.json` via the python-from-json curation
stage. API signatures are extracted to `abbrev`s; bodies are `sorry`
stubs wrapped in `!benchmark code` markers for the LLM to fill.
-/

namespace BooleanAlgebra

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
abbrev CompareStringSig := String → String → Option String
abbrev CheckSig := List String → List String
abbrev DecimalToBinarySig := Int → List Float → List String
abbrev IsForTableSig := String → String → Int → Bool
abbrev SelectionSig := List (List Int) → List String → List String
abbrev PrimeImplicantChartSig := List String → List String → List (List Int)

end BooleanAlgebra

-- !benchmark @start global_aux
private def BooleanAlgebra.listGetD {α : Type} (xs : List α) (i : Nat) (default : α) : α :=
  (xs[i]?).getD default
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=compare_string
-- !benchmark @end code_aux def=compare_string

def BooleanAlgebra.compare_string : BooleanAlgebra.CompareStringSig :=
-- !benchmark @start code def=compare_string
  fun s1 s2 =>
    let pairs := s1.toList.zip s2.toList
    let merged : List Char := pairs.map (fun (c1, c2) => if c1 = c2 then c1 else '_')
    let diffCount : Nat := pairs.foldl (init := 0) fun acc (c1, c2) =>
      if c1 = c2 then acc else acc + 1
    if diffCount > 1 then none else some (String.ofList merged)
-- !benchmark @end code def=compare_string

-- !benchmark @start code_aux def=check
/-- One pass of the Quine–McCluskey combine step. Returns `(primeImplicants, nextRound)`
    where `nextRound` is `none` if no merges happened (terminate) or `some xs` for the
    deduplicated merge results. -/
private def BooleanAlgebra.checkOneRound (binary : List String) :
    List String × Option (List String) :=
  let n := binary.length
  let initFlags : List Bool := List.replicate n true
  let pairsRes :=
    (List.range n).foldl (init := (initFlags, ([] : List String))) fun (flags, temp) i =>
      ((List.range n).foldl (init := (flags, temp)) fun (flags, temp) j =>
        if j ≤ i then (flags, temp)
        else
          match BooleanAlgebra.compare_string
                  (BooleanAlgebra.listGetD binary i "")
                  (BooleanAlgebra.listGetD binary j "") with
          | none => (flags, temp)
          | some s =>
            let flags' := flags.set i false |>.set j false
            (flags', temp ++ [s]))
  let (flags, temp) := pairsRes
  let pi : List String :=
    (List.range n).foldl (init := ([] : List String)) fun acc i =>
      if BooleanAlgebra.listGetD flags i false then
        acc ++ [BooleanAlgebra.listGetD binary i ""]
      else acc
  if temp.isEmpty then (pi, none)
  else
    let deduped : List String :=
      temp.foldl (init := ([] : List String)) fun acc s =>
        if acc.contains s then acc else acc ++ [s]
    (pi, some deduped)

private partial def BooleanAlgebra.checkLoop
    (binary : List String) (acc : List String) : List String :=
  let (pi, next) := BooleanAlgebra.checkOneRound binary
  let acc' := acc ++ pi
  match next with
  | none => acc'
  | some xs => BooleanAlgebra.checkLoop xs acc'
-- !benchmark @end code_aux def=check

def BooleanAlgebra.check : BooleanAlgebra.CheckSig :=
-- !benchmark @start code def=check
  fun binary => BooleanAlgebra.checkLoop binary []
-- !benchmark @end code def=check

-- !benchmark @start code_aux def=decimal_to_binary
-- !benchmark @end code_aux def=decimal_to_binary

def BooleanAlgebra.decimal_to_binary : BooleanAlgebra.DecimalToBinarySig :=
-- !benchmark @start code def=decimal_to_binary
  fun n minterms =>
    let nNat := n.toNat
    minterms.map fun m =>
      let mInt : Int := m.toInt64.toInt
      let (_, s) := (List.range nNat).foldl (init := (mInt, "")) fun (cur, acc) _ =>
        let bit := cur % 2
        let nextCur := cur / 2
        (nextCur, toString bit ++ acc)
      s
-- !benchmark @end code def=decimal_to_binary

-- !benchmark @start code_aux def=is_for_table
-- !benchmark @end code_aux def=is_for_table

def BooleanAlgebra.is_for_table : BooleanAlgebra.IsForTableSig :=
-- !benchmark @start code def=is_for_table
  fun s1 s2 count =>
    let zipped := s1.toList.zip s2.toList
    let diffs : Int := zipped.foldl (init := 0) fun acc (c1, c2) =>
      if c1 = c2 then acc else acc + 1
    diffs == count
-- !benchmark @end code def=is_for_table

-- !benchmark @start code_aux def=selection
/-- Replicates the Python algorithm's iterative phase. Returns the chosen prime
    implicants. Terminates when no row has any 1 left. -/
private partial def BooleanAlgebra.selectionLoop
    (chart : List (List Int)) (pis : List String) (acc : List String) : List String :=
  let counts : List Int := chart.map (fun row =>
    row.foldl (init := 0) fun a v => if v = 1 then a + 1 else a)
  let maxN : Int := counts.foldl (init := 0) fun a v => if v > a then v else a
  if maxN = 0 then acc
  else
    let rem : Nat :=
      (counts.zipIdx.findSome? (fun (c, i) => if c = maxN then some i else none)).getD 0
    let chosen := BooleanAlgebra.listGetD pis rem ""
    let chosenRow := BooleanAlgebra.listGetD chart rem []
    let chartLen := chart.length
    let rowLen := match chart with
      | [] => 0
      | r :: _ => r.length
    let chart' : List (List Int) :=
      (List.range chartLen).map fun i =>
        let row := BooleanAlgebra.listGetD chart i []
        (List.range rowLen).map fun j =>
          if BooleanAlgebra.listGetD chosenRow j 0 = 1 then 0
          else BooleanAlgebra.listGetD row j 0
    BooleanAlgebra.selectionLoop chart' pis (acc ++ [chosen])
-- !benchmark @end code_aux def=selection

def BooleanAlgebra.selection : BooleanAlgebra.SelectionSig :=
-- !benchmark @start code def=selection
  fun chart pis =>
    let m := chart.length
    if m = 0 then []
    else
      let firstRow := BooleanAlgebra.listGetD chart 0 []
      let n := firstRow.length
      -- Compute select[i]: i = max j' such that chart[j'][col]=1 for some column col
      -- whose count of 1s is exactly 1, and chart[i][col]=1.
      let select : List Bool :=
        (List.range m).map fun i =>
          (List.range n).any fun j =>
            let colCount := chart.foldl (init := 0) fun acc row =>
              if BooleanAlgebra.listGetD row j 0 = 1 then acc + 1 else acc
            let row_i := BooleanAlgebra.listGetD chart i []
            let row_i_j := BooleanAlgebra.listGetD row_i j 0
            let lastIdx : Int := chart.zipIdx.foldl (init := -1) fun acc (row, k) =>
              if BooleanAlgebra.listGetD row j 0 = 1 then (k : Int) else acc
            decide (colCount = 1) && decide (row_i_j = 1) && decide (i = lastIdx.toNat)
      let (chartAfterPhase1, accPhase1) :=
        (List.range m).foldl (init := (chart, ([] : List String))) fun (curChart, curAcc) i =>
          if BooleanAlgebra.listGetD select i false then
            let row := BooleanAlgebra.listGetD curChart i []
            let newChart : List (List Int) :=
              curChart.map fun r =>
                (List.range n).map fun j =>
                  if BooleanAlgebra.listGetD row j 0 = 1 then 0
                  else BooleanAlgebra.listGetD r j 0
            (newChart, curAcc ++ [BooleanAlgebra.listGetD pis i ""])
          else (curChart, curAcc)
      BooleanAlgebra.selectionLoop chartAfterPhase1 pis accPhase1
-- !benchmark @end code def=selection

-- !benchmark @start code_aux def=prime_implicant_chart
-- !benchmark @end code_aux def=prime_implicant_chart

def BooleanAlgebra.prime_implicant_chart : BooleanAlgebra.PrimeImplicantChartSig :=
-- !benchmark @start code def=prime_implicant_chart
  fun pis binary =>
    pis.map fun pi =>
      let count : Int := pi.toList.foldl (init := 0) fun a c => if c = '_' then a + 1 else a
      binary.map fun b => if BooleanAlgebra.is_for_table pi b count then 1 else 0
-- !benchmark @end code def=prime_implicant_chart
