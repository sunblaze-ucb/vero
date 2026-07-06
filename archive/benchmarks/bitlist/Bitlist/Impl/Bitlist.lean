-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Bitlist.Impl.Bitlist

Core type, signatures, and implementations for the `bitlist` Python
library — a bit-addressable sequence backed by a big-endian `List Bool`
(most-significant bit at index 0). Supports concatenation, length,
integer conversion, and index/slice access.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Function
bodies are the curator's reference implementations; the pipeline
replaces them with `sorry` inside the `code` markers before presenting
the benchmark to the LLM.
-/

-- ── Core type (DO NOT MODIFY) ─────────────────────────────────

/-- A bit vector represented as a list of booleans in big-endian order
    (most-significant bit at index 0). -/
abbrev Bitlist := List Bool

namespace Bitlist

-- ── API signatures (DO NOT MODIFY) ────────────────────────────

/-- Construct a Bitlist from a big-endian list of booleans. -/
abbrev MkSig       := List Bool → Bitlist

/-- Return the number of bits in the bit vector. -/
abbrev LengthSig   := Bitlist → Nat

/-- Concatenate two bit vectors (append `other` to the right of `self`). -/
abbrev AddSig      := Bitlist → Bitlist → Bitlist

/-- Index or slice a bit vector.
    - `Sum.inl i` : integer index (positive = from MSB, negative = from LSB).
    - `Sum.inr (start, stop, step)` : Python-style slice (None = default bound).
    Returns `Except.error` on out-of-bounds integer index. -/
abbrev GetitemSig  := Bitlist
                    → Sum Int (Option Int × Option Int × Option Int)
                    → Except String (Sum Bool Bitlist)

/-- Interpret the big-endian bit vector as a natural number. -/
abbrev ToIntSig    := Bitlist → Nat

end Bitlist

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── Implementations (LLM task) ─────────────────────────────────

-- !benchmark @start code_aux def=make
-- !benchmark @end code_aux def=make

def Bitlist.mk : Bitlist.MkSig :=
-- !benchmark @start code def=make
  fun bits => bits
-- !benchmark @end code def=make

-- !benchmark @start code_aux def=length
-- !benchmark @end code_aux def=length

def Bitlist.length : Bitlist.LengthSig :=
-- !benchmark @start code def=length
  fun b => List.length b
-- !benchmark @end code def=length

-- !benchmark @start code_aux def=add
-- !benchmark @end code_aux def=add

def Bitlist.add : Bitlist.AddSig :=
-- !benchmark @start code def=add
  fun self other => List.append self other
-- !benchmark @end code def=add

-- !benchmark @start code_aux def=bitlist_getitem
-- !benchmark @end code_aux def=bitlist_getitem

def bitlist_getitem : Bitlist.GetitemSig :=
-- !benchmark @start code def=bitlist_getitem
  fun self key =>
    let n := List.length self
    match key with
    | Sum.inl i =>
      -- Positive index: 0 = MSB (left-most bit).
      -- Negative index: -1 = LSB (right-most bit), following Python semantics.
      -- Out-of-bounds positive → error; out-of-bounds negative → false (Python returns 0).
      if 0 ≤ i then
        if h : i.toNat < n then
          Except.ok (Sum.inl (self.get ⟨i.toNat, h⟩))
        else
          Except.error "bitlist index out of range"
      else
        let absI := i.natAbs
        if absI ≤ n then
          if h : n - absI < n then
            Except.ok (Sum.inl (self.get ⟨n - absI, h⟩))
          else
            -- absI = 0 branch (n - 0 = n, not in range): should not occur when absI ≤ n and absI > 0
            Except.error "bitlist index out of range"
        else
          -- Python returns virtual 0 bit for deeply-negative out-of-range indices.
          Except.ok (Sum.inl false)
    | Sum.inr (mstart, mstop, _mstep) =>
      -- Slice: normalize None bounds and clamp to [0, n].
      let normIdx : Int → Nat := fun i =>
        if 0 ≤ i then min i.toNat n else n - min i.natAbs n
      let s  := mstart.map normIdx |>.getD 0
      let e  := mstop.map normIdx |>.getD n
      let e' := max s e
      Except.ok (Sum.inr ((self.drop s).take (e' - s)))
-- !benchmark @end code def=bitlist_getitem

-- !benchmark @start code_aux def=bitlistToInt
-- !benchmark @end code_aux def=bitlistToInt

def bitlistToInt : Bitlist.ToIntSig :=
-- !benchmark @start code def=bitlistToInt
  -- Big-endian fold: MSB contributes 2^(n-1), LSB contributes 2^0.
  fun bl => bl.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0
-- !benchmark @end code def=bitlistToInt
