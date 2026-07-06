-- !benchmark @start imports
-- !benchmark @end imports

/-!
# SpecialNumbers.Impl.WeirdNumber

A weird number is abundant (sum of proper divisors > n) but not semi-perfect
(no subset of proper divisors sums to n). Example: 70 is weird.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- !benchmark @start global_aux
/-- Integer square root via Newton's method for use in factors computation.
    @review human: terminates because (x + n/x)/2 < x whenever x > sqrt(n). -/
private partial def wIsqrt (n x : Nat) : Nat :=
  let next := (x + n / x) / 2
  if next >= x then x else wIsqrt n next
-- !benchmark @end global_aux

namespace SpecialNumbers

-- ── API signatures (no markers — fixed vocabulary) ────────────

abbrev FactorsSig    := Int → List Int
abbrev AbundantSig   := Int → Bool
abbrev SemiPerfectSig := Int → Bool
abbrev WeirdSig      := Int → Bool

end SpecialNumbers

-- ── Implementation stubs (LLM task) ───────────────────────────

-- !benchmark @start code_aux def=factors
-- !benchmark @end code_aux def=factors

def SpecialNumbers.factors : SpecialNumbers.FactorsSig :=
-- !benchmark @start code def=factors
  fun number =>
    if number <= 0 then [1]
    else
      let n := number.toNat
      let sqrtN := if n == 0 then 0 else wIsqrt n (n / 2 + 1)
      -- range(2, sqrtN + 1) has sqrtN - 1 elements (saturates at 0 for sqrtN < 2)
      let pairs : List Int := (List.range' 2 (sqrtN - 1)).foldl
        (fun (acc : List Int) (i : Nat) =>
          if n % i == 0 then
            let q := n / i
            if q != i then acc ++ [(i : Int), (q : Int)]
            else acc ++ [(i : Int)]
          else acc)
        []
      List.mergeSort ([(1 : Int)] ++ pairs)
-- !benchmark @end code def=factors

-- !benchmark @start code_aux def=abundant
-- !benchmark @end code_aux def=abundant

def SpecialNumbers.abundant : SpecialNumbers.AbundantSig :=
-- !benchmark @start code def=abundant
  fun n =>
    let fs := SpecialNumbers.factors n
    fs.foldl (fun (acc : Int) x => acc + x) 0 > n
-- !benchmark @end code def=abundant

-- !benchmark @start code_aux def=semi_perfect
-- !benchmark @end code_aux def=semi_perfect

def SpecialNumbers.semi_perfect : SpecialNumbers.SemiPerfectSig :=
-- !benchmark @start code def=semi_perfect
  fun number =>
    if number < 0 then false
    else
      -- 2D DP subset sum: can some subset of factors(number) sum to number?
      -- Flatten 2D array: dp[i * cols + j] = can first i factors sum to j?
      let n := number.toNat
      let vs : List Nat := (SpecialNumbers.factors number).map Int.toNat
      let r := vs.length
      let cols := n + 1
      -- Initialize: all false, then set dp[i * cols + 0] = true for all i
      let dp0 : Array Bool := (List.replicate ((r + 1) * cols) false).toArray
      let dp1 := (List.range (r + 1)).foldl
        (fun (dp : Array Bool) (i : Nat) => dp.set! (i * cols) true) dp0
      -- Fill rows 1..r
      let dpFinal := (List.range' 1 r).foldl
        (fun (dp : Array Bool) (i : Nat) =>
          let v := vs.getD (i - 1) 0
          (List.range' 1 n).foldl
            (fun (dp' : Array Bool) (j : Nat) =>
              let prev := dp'.getD ((i - 1) * cols + j) false
              let newVal :=
                if j < v then prev
                else prev || dp'.getD ((i - 1) * cols + (j - v)) false
              dp'.set! (i * cols + j) newVal)
            dp)
        dp1
      dpFinal.getD (r * cols + n) false
-- !benchmark @end code def=semi_perfect

-- !benchmark @start code_aux def=weird
-- !benchmark @end code_aux def=weird

def SpecialNumbers.weird : SpecialNumbers.WeirdSig :=
-- !benchmark @start code def=weird
  fun number =>
    SpecialNumbers.abundant number && !SpecialNumbers.semi_perfect number
-- !benchmark @end code def=weird
