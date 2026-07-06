-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DepositSc.Impl.Bits

Bit-list primitives used by the Merkle-tree machinery. A `Bit` is a
`Fin 2` (so `0` and `1` are the only inhabitants and arithmetic like
`1 - b.val` is well-defined). A `Path` is a `List Bit` representing a
left/right trail from the root of a complete binary tree.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations; the pipeline
replaces them with `sorry` inside the `code` markers before presenting
the benchmark to the LLM.

Upstream: `src/dafny/smart/seqofbits/SeqOfBits.dfy`,
         `src/dafny/smart/helpers/Helpers.dfy`.
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A single bit. Dafny: `newtype bit = i:int | 0 <= i < 2`. -/
abbrev Bit := Fin 2

/-- A path through a complete binary tree, MSB-first (index 0 is the
    step taken at the root, the final entry is the step into the leaf
    parent). Dafny: `type path = seq<bit>`. -/
abbrev Path := List Bit

/-- Binary merge function. Dafny: `(int, int) -> int`. -/
abbrev MergeFn := Int → Int → Int

namespace DepositSc

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- Raise 2 to a natural power. -/
abbrev Power2Sig        := Nat → Nat

/-- Big-endian `List Bit → Nat`. -/
abbrev BitListToNatSig  := List Bit → Nat

/-- `natToBitList n len`: MSB-first `len`-bit binary of `n`.
    Valid for `n < 2^len`. -/
abbrev NatToBitListSig  := Nat → Nat → List Bit

/-- Binary successor on a bit list (requires at least one `0` bit). -/
abbrev NextPathSig      := List Bit → List Bit

/-- Element-wise `if c[i] = 0 then a[i] else b[i]` (length
    determined by `c`; callers must provide `a` and `b` of matching
    length). -/
abbrev ZipCondSig       := List Bit → List Int → List Int → List Int

/-- Iterated `f` applied to the default value (`defaultValue f d 0 = d`,
    `defaultValue f d (k+1) = f (defaultValue f d k) (defaultValue f d k)`). -/
abbrev DefaultValueSig  := MergeFn → Int → Nat → Int

/-- `zeroes f d h = [defaultValue f d 0, …, defaultValue f d h]`
    (length `h + 1`), **ascending** — index 0 is the leaf-level default,
    index `h` is the top-level default.

    Convention differs from upstream Dafny, which stores `zeroes` in
    descending order (`zeroes[i] = defaultValue(h - i)`). The Lean
    Merkle module (`Impl/Merkle.lean`) uses the same reversed sibling-
    array convention, so `zeroH[0]` is the correct leaf-level
    right-sibling default for this module's algorithms. -/
abbrev ZeroesSig        := MergeFn → Int → Nat → List Int

end DepositSc

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementations ──────────────────────────────────────────

-- !benchmark @start code_aux def=power2
-- !benchmark @end code_aux def=power2

def DepositSc.power2 : DepositSc.Power2Sig :=
-- !benchmark @start code def=power2
  fun n => 2 ^ n
-- !benchmark @end code def=power2

-- !benchmark @start code_aux def=bitListToNat
-- !benchmark @end code_aux def=bitListToNat

def DepositSc.bitListToNat : DepositSc.BitListToNatSig :=
-- !benchmark @start code def=bitListToNat
  fun bs => bs.foldl (fun acc b => 2 * acc + b.val) 0
-- !benchmark @end code def=bitListToNat

-- !benchmark @start code_aux def=natToBitList
-- !benchmark @end code_aux def=natToBitList

def DepositSc.natToBitList : DepositSc.NatToBitListSig :=
-- !benchmark @start code def=natToBitList
  fun n len =>
    let rec go : Nat → Nat → List Bit → List Bit
      | 0,     _, acc => acc
      | k + 1, m, acc =>
        let b : Bit := ⟨m % 2, by omega⟩
        go k (m / 2) (b :: acc)
    go len n []
-- !benchmark @end code def=natToBitList

-- !benchmark @start code_aux def=nextPath
-- !benchmark @end code_aux def=nextPath

def DepositSc.nextPath : DepositSc.NextPathSig :=
-- !benchmark @start code def=nextPath
  fun p =>
    let n := DepositSc.bitListToNat p
    DepositSc.natToBitList (n + 1) p.length
-- !benchmark @end code def=nextPath

-- !benchmark @start code_aux def=zipCond
-- !benchmark @end code_aux def=zipCond

def DepositSc.zipCond : DepositSc.ZipCondSig :=
-- !benchmark @start code def=zipCond
  fun c a b =>
    let rec go : List Bit → List Int → List Int → List Int
      | [],        _,       _       => []
      | _ :: _,    [],      _       => []
      | _ :: _,    _,       []      => []
      | ci :: cs, ai :: as, bi :: bs =>
        (if ci.val = 0 then ai else bi) :: go cs as bs
    go c a b
-- !benchmark @end code def=zipCond

-- !benchmark @start code_aux def=defaultValue
-- !benchmark @end code_aux def=defaultValue

def DepositSc.defaultValue : DepositSc.DefaultValueSig :=
-- !benchmark @start code def=defaultValue
  fun f d =>
    let rec go : Nat → Int
      | 0     => d
      | k + 1 => let v := go k; f v v
    go
-- !benchmark @end code def=defaultValue

-- !benchmark @start code_aux def=zeroes
-- !benchmark @end code_aux def=zeroes

def DepositSc.zeroes : DepositSc.ZeroesSig :=
-- !benchmark @start code def=zeroes
  fun f d h =>
    (List.range (h + 1)).map (DepositSc.defaultValue f d)
-- !benchmark @end code def=zeroes
