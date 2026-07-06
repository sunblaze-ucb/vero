import DafnyVMC.Impl.UniformModel

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DafnyVMC.Impl.FisherYatesModel

Fisher-Yates shuffle in the Hurd monad.
Corresponds to `src/Util/FisherYates/Model.dfy`.

- `swap` exchanges elements at positions `i` and `j` in a list (total;
  returns `s` unchanged on out-of-bounds).
- `shuffleCurried` is the recursive Fisher-Yates step, sampling a random
  index via `intervalSample` and swapping; terminates when fewer than 2
  elements remain.
- `shuffle` is the top-level entry, calling `shuffleCurried` from position 0.

`shuffleCurried` and `shuffle` are `noncomputable` because they depend on
`intervalSample`, which is built on the axiomatised `sample` measure.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Vocabulary helpers (DO NOT MODIFY) ────────────────────────────────

/-- Exchange elements at positions `i` and `j` in list `s`.
    Returns `s` unchanged if either index is out of bounds.
    Corresponds to Dafny's `Swap` function in `FisherYates.Model`. -/
def swap {α : Type} (s : List α) (i j : Nat) : List α :=
  if hi : i < s.length then
    if hj : j < s.length then
      s.set i (s.get ⟨j, hj⟩) |>.set j (s.get ⟨i, hi⟩)
    else s
  else s

/-- `swap` preserves the length of a list.
    Used for the well-founded measure of `shuffleCurried`. -/
private theorem swap_length {α : Type} (s : List α) (i j : Nat) :
    (swap s i j).length = s.length := by
  unfold swap
  split_ifs <;> simp [List.length_set]

/-- Recursive Fisher-Yates shuffle step, starting at index `i`.
    At each step, samples a random index `j` from `[i, xs.length)` via
    `intervalSample`, swaps `xs[i]` with `xs[j]`, and recurses with `i + 1`.
    Terminates when fewer than 2 elements remain (`xs.length - i ≤ 1`).

    Corresponds to Dafny's `ShuffleCurried` in `FisherYates.Model`. -/
def shuffleCurried {α : Type} (xs : List α) (i : Nat) : Hurd (List α) :=
  if h : xs.length - i > 1 then
    bind (intervalSample (i : Int) (xs.length : Int) (by omega))
         (fun j => shuffleCurried (swap xs i j.toNat) (i + 1))
  else return' xs
termination_by xs.length - i
decreasing_by
  rw [swap_length]
  omega

/-- Full Fisher-Yates shuffle: calls `shuffleCurried` from position 0.
    Corresponds to Dafny's `Shuffle` in `FisherYates.Model`. -/
def shuffle {α : Type} (xs : List α) : Hurd (List α) :=
  shuffleCurried xs 0
