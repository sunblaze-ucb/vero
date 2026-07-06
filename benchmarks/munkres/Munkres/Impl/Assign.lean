-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Munkres.Impl.Assign

The Munkres / Hungarian / Kuhn–Munkres algorithm for the classical *assignment
problem*, ported from the `munkres` library (PyPI `munkres`, bmc/munkres,
Apache-2.0, `munkres.py`). Given an n×n integer cost matrix, it finds an
assignment (a one row → one column bijection) of **minimum total cost**.

Representation (mathlib-free, all `Nat`/`Int`/`List`):
- A cost matrix is a `List (List Nat)` (row-major). `compute` first pads it to a
  square matrix with `padMatrix`, then runs the primal-dual method.
- The internal working matrix `C` is `List (List Int)` (step 1 and step 6
  subtract row/column potentials, so intermediate entries live in `Int`).
- Covers/stars/primes are modelled with plain `List`s and index arithmetic,
  mirroring the mutable arrays `row_covered`, `col_covered`, `marked`, `path`
  of the Python class.

APIs in this module: `padMatrix` (rectangular → square, pad with 0),
`makeCostMatrix` (profit → cost via `globalMax − value`, munkres' default
`inversion_function`), `compute` (the optimal assignment as `(row, col)`
pairs), and `assignmentCost` (the total-cost fold over an assignment).

The step machine is driven by a fuel-bounded loop (`runSteps`); `2·n·n + 8`
iterations are always enough for an n×n matrix (each augmenting round consumes
at least one uncovered zero and there are at most `n²` cells). All functions are
total, terminating `def`s; no `Float`.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

namespace Munkres

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `padMatrix M`: pad a possibly non-square `Nat` matrix to a square one, using
    the pad value `0`. -/
abbrev PadMatrixSig := List (List Nat) → List (List Nat)

/-- `makeCostMatrix P`: turn a profit matrix into a cost matrix by inverting each
    entry as `globalMax P − value` (munkres' default inversion). -/
abbrev MakeCostMatrixSig := List (List Nat) → List (List Nat)

/-- `compute M`: the minimum-cost assignment for cost matrix `M`, as a list of
    `(row, column)` pairs. -/
abbrev ComputeSig := List (List Nat) → List (Nat × Nat)

/-- `assignmentCost M pairs`: total cost of the assignment `pairs` under matrix
    `M` — the sum of `M[r][c]` over each `(r, c)`. -/
abbrev AssignmentCostSig := List (List Nat) → List (Nat × Nat) → Nat

end Munkres

-- !benchmark @start global_aux
namespace Munkres

-- ── Small list/matrix helpers (frozen) ───────────────────────

/-- `getD? xs i`: the `i`-th element of `xs`, or `0` when out of range (for
    `Nat`-valued lists). Frozen helper. -/
def natGet (xs : List Nat) (i : Nat) : Nat := xs.getD i 0

/-- `intGet xs i`: the `i`-th element of an `Int` list, or `0`. Frozen helper. -/
def intGet (xs : List Int) (i : Nat) : Int := xs.getD i 0

/-- `matGetN M i j`: entry `(i, j)` of a `Nat` matrix, or `0`. Frozen helper. -/
def matGetN (M : List (List Nat)) (i j : Nat) : Nat := natGet (M.getD i []) j

/-- `matGetI C i j`: entry `(i, j)` of an `Int` matrix, or `0`. Frozen helper. -/
def matGetI (C : List (List Int)) (i j : Nat) : Int := intGet (C.getD i []) j

/-- `setNth xs i v`: replace the `i`-th element of `xs` with `v` (no-op if out of
    range). Frozen helper mirroring `xs[i] = v`. -/
def setNth {α : Type} (xs : List α) (i : Nat) (v : α) : List α :=
  xs.set i v

/-- `matSet C i j v`: set entry `(i, j)` of an `Int` matrix to `v`. Frozen
    helper. -/
def matSet (C : List (List Int)) (i j : Nat) (v : Int) : List (List Int) :=
  C.set i ((C.getD i []).set j v)

/-- `listMaxN xs`: maximum of a `Nat` list (`0` for the empty list). Frozen
    helper. -/
def listMaxN (xs : List Nat) : Nat := xs.foldl Nat.max 0

/-- `listMinN xs`: minimum of a nonempty `Nat` list; `0` for the empty list.
    Frozen helper mirroring `min(row)`. -/
def listMinN (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h :: t => t.foldl Nat.min h

/-- `range n = [0, 1, …, n-1]`. Frozen helper. -/
def range (n : Nat) : List Nat := List.range n

/-- `sumN xs`: sum of a `Nat` list. Frozen helper. -/
def sumN (xs : List Nat) : Nat := xs.foldl (· + ·) 0

end Munkres
-- !benchmark @end global_aux

namespace Munkres

-- ══════════════════════════════════════════════════════════════════
-- padMatrix
-- ══════════════════════════════════════════════════════════════════

-- !benchmark @start code_aux def=padMatrix
/-- `maxCols M`: the widest row length in `M`. Frozen helper for `padMatrix`. -/
def maxCols (M : List (List Nat)) : Nat := listMaxN (M.map List.length)

/-- `padRow row w`: pad `row` on the right with `0`s up to length `w` (no-op if
    already ≥ `w`). Frozen helper. -/
def padRow (row : List Nat) (w : Nat) : List Nat :=
  if w > row.length then row ++ List.replicate (w - row.length) 0 else row
-- !benchmark @end code_aux def=padMatrix

def padMatrix : PadMatrixSig :=
-- !benchmark @start code def=padMatrix
  fun M =>
    let n := Nat.max (maxCols M) M.length
    let padded := M.map (fun row => padRow row n)
    padded ++ List.replicate (n - M.length) (List.replicate n 0)
-- !benchmark @end code def=padMatrix

-- ══════════════════════════════════════════════════════════════════
-- makeCostMatrix
-- ══════════════════════════════════════════════════════════════════

-- !benchmark @start code_aux def=makeCostMatrix
/-- `globalMax M`: the maximum entry over the whole matrix (`0` when empty).
    Frozen helper — munkres computes `max(max(row) for row in matrix)`. -/
def globalMax (M : List (List Nat)) : Nat := listMaxN (M.map listMaxN)
-- !benchmark @end code_aux def=makeCostMatrix

def makeCostMatrix : MakeCostMatrixSig :=
-- !benchmark @start code def=makeCostMatrix
  fun P =>
    let mx := globalMax P
    P.map (fun row => row.map (fun v => mx - v))
-- !benchmark @end code def=makeCostMatrix

-- ══════════════════════════════════════════════════════════════════
-- assignmentCost
-- ══════════════════════════════════════════════════════════════════

-- !benchmark @start code_aux def=assignmentCost
-- !benchmark @end code_aux def=assignmentCost

def assignmentCost : AssignmentCostSig :=
-- !benchmark @start code def=assignmentCost
  fun M pairs => sumN (pairs.map (fun p => matGetN M p.1 p.2))
-- !benchmark @end code def=assignmentCost

-- ══════════════════════════════════════════════════════════════════
-- compute — the Munkres primal-dual step machine
-- ══════════════════════════════════════════════════════════════════

-- !benchmark @start code_aux def=compute

/-- Mutable-state record for the Munkres steps, mirroring the fields of the
    Python `Munkres` object: `C` the working matrix, `rowCov`/`colCov` the
    covers, `marked` the star/prime marks (0 = none, 1 = star, 2 = prime),
    `n` the side length, `z0r`/`z0c` the primed-zero cursor. Frozen. -/
structure MState where
  C      : List (List Int)
  rowCov : List Bool
  colCov : List Bool
  marked : List (List Int)
  n      : Nat
  z0r    : Nat
  z0c    : Nat
deriving Inhabited

/-- Initial state: pad `M`, cast to `Int`, all covers off, all marks 0. Frozen. -/
def initState (M : List (List Nat)) : MState :=
  let P := padMatrix M
  let n := P.length
  { C      := P.map (fun row => row.map (fun v => (Int.ofNat v)))
    rowCov := List.replicate n false
    colCov := List.replicate n false
    marked := List.replicate n (List.replicate n (0 : Int))
    n      := n
    z0r    := 0
    z0c    := 0 }

/-- `clearCovers`: reset all covers to `false`. Frozen (munkres `__clear_covers`). -/
def clearCovers (s : MState) : MState :=
  { s with rowCov := List.replicate s.n false, colCov := List.replicate s.n false }

/-- `erasePrimes`: turn every prime (mark `2`) back to `0`. Frozen
    (`__erase_primes`). -/
def erasePrimes (s : MState) : MState :=
  { s with marked := s.marked.map (fun row => row.map (fun m => if m == 2 then 0 else m)) }

/-- Step 1: subtract each row's minimum from every entry in that row. Frozen. -/
def step1 (s : MState) : MState :=
  let C' := s.C.map (fun row =>
    let mn := row.foldl min (row.headD 0)
    row.map (fun x => x - mn))
  { s with C := C' }

/-- `findZeroStar2`: the star-placing scan of step 2. For each cell in row order,
    if the entry is `0` and neither its row nor column is covered, star it and
    cover both. Frozen worklist mirroring the nested loop of `__step2`. -/
def step2Aux : MState → Nat → Nat → MState
  | s, i, j =>
    if i ≥ s.n then s
    else if j ≥ s.n then step2Aux s (i + 1) 0
    else
      if matGetI s.C i j == 0 ∧ s.colCov.getD j false = false ∧ s.rowCov.getD i false = false then
        let s := { s with marked := matSet s.marked i j 1
                          colCov := setNth s.colCov j true
                          rowCov := setNth s.rowCov i true }
        -- `break` out of the inner (column) loop: advance to next row
        step2Aux s (i + 1) 0
      else
        step2Aux s i (j + 1)
termination_by s i j => (s.n - i, s.n - j)

/-- Step 2: star zeros (one per uncovered row/column), then clear covers. Frozen. -/
def step2 (s : MState) : MState := clearCovers (step2Aux s 0 0)

/-- `countStarsCoverCols`: cover every column that contains a star, counting the
    newly covered columns. Frozen scan of `__step3`. -/
def step3Aux : MState → Nat → Nat → Nat → (MState × Nat)
  | s, i, j, count =>
    if i ≥ s.n then (s, count)
    else if j ≥ s.n then step3Aux s (i + 1) 0 count
    else
      if matGetI s.marked i j == 1 ∧ s.colCov.getD j false = false then
        step3Aux { s with colCov := setNth s.colCov j true } i (j + 1) (count + 1)
      else
        step3Aux s i (j + 1) count
termination_by s i j _ => (s.n - i, s.n - j)

/-- `starInRow s r`: column of the first star in row `r`, or `-1`. Frozen. -/
def starInRow (s : MState) (r : Nat) : Int :=
  (((s.marked.getD r []).zipIdx).find? (fun p => p.1 == 1)).map (fun p => (p.2 : Int)) |>.getD (-1)

/-- `starInCol s c`: row of the first star in column `c`, or `-1`. Frozen. -/
def starInCol (s : MState) (c : Nat) : Int :=
  match (List.range s.n).find? (fun i => matGetI s.marked i c == 1) with
  | some i => (i : Int)
  | none => -1

/-- `primeInRow s r`: column of the first prime in row `r`, or `-1`. Frozen. -/
def primeInRow (s : MState) (r : Nat) : Int :=
  (((s.marked.getD r []).zipIdx).find? (fun p => p.1 == 2)).map (fun p => (p.2 : Int)) |>.getD (-1)

/-- `scanRowZero s i j0 acc j fuel`: sweep the columns of row `i` cyclically
    starting at `j0` (checking the current `j`, then advancing `j := (j+1) % n`
    until it wraps back to `j0`). This mirrors the inner `while True` loop of
    munkres' `__find_a_zero`, which re-checks on **every** iteration and so keeps
    the **last** uncovered zero seen in the sweep (`acc`). Returns the accumulated
    match (`(-1,-1)` if none). Frozen. -/
def scanRowZero (s : MState) (i j0 : Nat) : (Int × Int) → Nat → Nat → (Int × Int)
  | acc, _, 0 => acc
  | acc, j, (fuel + 1) =>
    let acc :=
      if matGetI s.C i j == 0 ∧ s.rowCov.getD i false = false ∧ s.colCov.getD j false = false
      then ((i : Int), (j : Int)) else acc
    let j' := (j + 1) % s.n
    if j' == j0 then acc else scanRowZero s i j0 acc j' fuel

/-- `findAZeroAux s i0 j0 i fuel`: sweep rows cyclically from `i0`, sweeping each
    row's columns from `j0` via `scanRowZero`; the **first row** whose sweep finds
    an uncovered zero fixes the result (munkres sets `done` and stops advancing
    rows once a zero is found). `(-1,-1)` when no row yields one. Faithful port of
    the outer `while not done` loop of `__find_a_zero`. Frozen. -/
def findAZeroAux (s : MState) (i0 j0 : Nat) : Nat → Nat → (Int × Int)
  | _, 0 => (-1, -1)
  | i, (fuel + 1) =>
    let hit := scanRowZero s i j0 (-1, -1) j0 (s.n + 1)
    if hit.1 ≥ 0 then hit
    else
      let i' := (i + 1) % s.n
      if i' == i0 then (-1, -1) else findAZeroAux s i0 j0 i' fuel

/-- `findAZero s i0 j0`: the uncovered zero munkres' `__find_a_zero` returns when
    called with cursor `(i0, j0)`. Frozen (fuel `n + 1` rows). -/
def findAZero (s : MState) (i0 j0 : Nat) : (Int × Int) :=
  if s.n == 0 then (-1, -1) else findAZeroAux s i0 j0 i0 (s.n + 1)

/-- Step 4: prime uncovered zeros. Returns the next step (`5` or `6`) and the
    updated state; on step `5` the primed-zero cursor `z0r`/`z0c` is set. Frozen
    port of `__step4`'s `while not done` loop. The `(row0, col0)` cursor is
    **threaded** exactly as munkres does: `find_a_zero` resumes from the position
    left after covering a starred row, not from `(0,0)`. Fuel-bounded by
    `n·n + 1`. -/
def step4Aux (s : MState) (row0 col0 : Nat) : Nat → (MState × Nat)
  | 0 => (s, 6)
  | fuel + 1 =>
    let z := findAZero s row0 col0
    if z.1 < 0 then (s, 6)
    else
      let row := z.1.toNat
      let col := z.2.toNat
      let s := { s with marked := matSet s.marked row col 2 }
      let sc := starInRow s row
      if sc ≥ 0 then
        let col' := sc.toNat
        let s := { s with rowCov := setNth s.rowCov row true
                          colCov := setNth s.colCov col' false }
        -- munkres keeps `row` and sets `col := star_col`; the next scan resumes
        -- from this cursor.
        step4Aux s row col' fuel
      else
        ({ s with z0r := row, z0c := col }, 5)

/-- Step 4 entry point (cursor starts at `(0, 0)`). Frozen. -/
def step4 (s : MState) : (MState × Nat) := step4Aux s 0 0 (s.n * s.n + 1)

/-- `buildPath`: the alternating star/prime series of step 5, returned as a list
    of `(row, col)` cells. Faithful port of `__step5`'s `while not done` loop,
    fuel-bounded by `2·n + 1`. Frozen. -/
def buildPathAux (s : MState) : List (Nat × Nat) → Nat → List (Nat × Nat)
  | path, 0 => path
  | path, fuel + 1 =>
    let last := path.getLast!  -- path is always nonempty here
    let r := starInCol s last.2
    if r ≥ 0 then
      let path := path ++ [(r.toNat, last.2)]
      let last2 := path.getLast!
      let c := primeInRow s last2.1
      buildPathAux s (path ++ [(last2.1, c.toNat)]) fuel
    else
      path
termination_by _ fuel => fuel

/-- Step 5: augment along the alternating path (unstar stars, star primes),
    clear covers, erase primes. Frozen port of `__step5`. -/
def step5 (s : MState) : MState :=
  let path := buildPathAux s [(s.z0r, s.z0c)] (2 * s.n + 1)
  let marked := path.foldl (fun mk cell =>
    let cur := matGetI mk cell.1 cell.2
    matSet mk cell.1 cell.2 (if cur == 1 then 0 else 1)) s.marked
  erasePrimes (clearCovers { s with marked := marked })

/-- `findSmallest s`: the smallest uncovered value in `C`. Frozen port of
    `__find_smallest`. -/
def findSmallest (s : MState) : Int :=
  let cells := (List.range s.n).flatMap (fun i =>
    (List.range s.n).filterMap (fun j =>
      if s.rowCov.getD i false = false ∧ s.colCov.getD j false = false
      then some (matGetI s.C i j) else none))
  match cells with
  | [] => 0
  | h :: t => t.foldl min h

/-- Step 6: add the smallest uncovered value to every covered row and subtract it
    from every uncovered column. Frozen port of `__step6` (without the DISALLOWED
    handling, which does not arise for plain `Nat` matrices). -/
def step6 (s : MState) : MState :=
  let mv := findSmallest s
  let C' := (List.range s.n).map (fun i =>
    (List.range s.n).map (fun j =>
      let x := matGetI s.C i j
      let x := if s.rowCov.getD i false = true then x + mv else x
      if s.colCov.getD j false = false then x - mv else x))
  { s with C := C' }

/-- `runSteps`: the driver `while not done` loop of `compute`. `step` is the
    current step id; the machine terminates when step 3 covers all `n` columns
    (`__step3` returns the sentinel `7`, encoded here as `stop`). Fuel-bounded by
    `2·n·n + 8`. Frozen. -/
def runSteps (s : MState) : Nat → Nat → MState
  | _, 0 => s
  | step, fuel + 1 =>
    match step with
    | 1 => runSteps (step1 s) 2 fuel
    | 2 => runSteps (step2 s) 3 fuel
    | 3 =>
      let (s, count) := step3Aux s 0 0 0
      if count ≥ s.n then s   -- done
      else runSteps s 4 fuel
    | 4 =>
      let (s, next) := step4 s
      runSteps s next fuel
    | 5 => runSteps (step5 s) 3 fuel
    | 6 => runSteps (step6 s) 4 fuel
    | _ => s

/-- Extract the starred cells `(i, j)` with `i < origLen` and `j < origWidth`, in
    row-major order — the assignment returned by `compute`. Frozen. -/
def extractResult (s : MState) (origLen origWidth : Nat) : List (Nat × Nat) :=
  (List.range origLen).flatMap (fun i =>
    (List.range origWidth).filterMap (fun j =>
      if matGetI s.marked i j == 1 then some (i, j) else none))

-- !benchmark @end code_aux def=compute

def compute : ComputeSig :=
-- !benchmark @start code def=compute
  fun M =>
    let origLen := M.length
    let origWidth := (M.headD []).length
    let s0 := initState M
    let s := runSteps s0 1 (2 * s0.n * s0.n + 8)
    extractResult s origLen origWidth
-- !benchmark @end code def=compute

end Munkres
