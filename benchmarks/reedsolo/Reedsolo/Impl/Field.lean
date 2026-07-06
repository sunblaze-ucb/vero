-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Reedsolo.Impl.Field

GF(2⁸) finite-field arithmetic and the Reed–Solomon systematic encoder.

The field GF(2⁸) has bytes `0 ≤ a < 256` as elements; polynomials over the
field are coefficient lists (highest-degree first). API: `gfMul`, `gfPow`,
`gfInverse` (field arithmetic), `rsGeneratorPoly` (the generator polynomial),
`rsEncodeMsg` (the systematic encoder). The field is the one determined by the
primitive polynomial `0x11d = x⁸ + x⁴ + x³ + x² + 1`; the primitive element is
`α = 2`. Behaviour is pinned by `Spec/Field.lean`.

Everything is discrete over `Nat` (a byte is a `Nat < 256`); there is no
`Float`. Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- A field element / byte: a `Nat` intended to range over `0 ≤ a < 256`.
    (Modelled as `Nat`, not a bounded type, so the field laws can be stated
    with explicit range hypotheses and proven structurally.) -/
abbrev GFByte := Nat

/-- A polynomial over GF(2⁸): a coefficient list, highest-degree first, each
    coefficient a field element. The empty list is the zero polynomial. -/
abbrev GFPoly := List Nat

namespace Reedsolo

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `gfMul a b`: the GF(2⁸) product of two bytes. -/
abbrev GfMulSig := Nat → Nat → Nat

/-- `gfPow a e`: the GF(2⁸) power `a^e` (`a^0 = 1`). -/
abbrev GfPowSig := Nat → Nat → Nat

/-- `gfInverse a`: the GF(2⁸) multiplicative inverse of a nonzero byte `a`
    (the unique `b` with `gfMul a b = 1`). -/
abbrev GfInverseSig := Nat → Nat

/-- `rsGeneratorPoly nsym`: the degree-`nsym` Reed–Solomon generator
    polynomial, as a coefficient list highest-degree-first. -/
abbrev RsGeneratorPolySig := Nat → List Nat

/-- `rsEncodeMsg msg nsym`: the systematic Reed–Solomon codeword for message
    `msg` with `nsym` parity symbols. -/
abbrev RsEncodeMsgSig := List Nat → Nat → List Nat

end Reedsolo

-- !benchmark @start global_aux
/-- The fixed GF(2⁸) primitive polynomial `x⁸ + x⁴ + x³ + x² + 1 = 0x11d`. -/
def primPoly : Nat := 0x11d

/-- The primitive element `α = 2 = x` of GF(2⁸). -/
def alpha : Nat := 2
-- !benchmark @end global_aux

-- ════════════════════════════════════════════════════════════════
-- gfMul
-- ════════════════════════════════════════════════════════════════

-- !benchmark @start code_aux def=gfMul
def clmulBits : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | (n+1), a, b => (if a.testBit n then b <<< n else 0) ^^^ clmulBits n a b

def clmul (a b : Nat) : Nat := clmulBits 8 a b

def reduceAux : Nat → Nat → Nat → Nat
  | 0, x, _ => x
  | (fuel+1), x, prim =>
      let x := if x.testBit (8 + fuel) then x ^^^ (prim <<< fuel) else x
      reduceAux fuel x prim

/-- The GF(2⁸) product of `a` and `b` in the field of primitive polynomial `prim`. -/
def clmulModPrim (a b prim : Nat) : Nat := reduceAux 7 (clmul a b) prim
-- !benchmark @end code_aux def=gfMul

def Reedsolo.gfMul : Reedsolo.GfMulSig :=
-- !benchmark @start code def=gfMul
  fun a b => clmulModPrim a b primPoly
-- !benchmark @end code def=gfMul

-- ════════════════════════════════════════════════════════════════
-- gfPow
-- ════════════════════════════════════════════════════════════════

-- !benchmark @start code_aux def=gfPow
-- !benchmark @end code_aux def=gfPow

def Reedsolo.gfPow : Reedsolo.GfPowSig :=
-- !benchmark @start code def=gfPow
  fun a e => Nat.rec 1 (fun _ acc => Reedsolo.gfMul acc a) e
-- !benchmark @end code def=gfPow

-- ════════════════════════════════════════════════════════════════
-- gfInverse
-- ════════════════════════════════════════════════════════════════

-- !benchmark @start code_aux def=gfInverse
def gfPowSq : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | (n+1), base, e =>
      let half := gfPowSq n (Reedsolo.gfMul base base) (e / 2)
      if e % 2 == 1 then Reedsolo.gfMul half base else half
-- !benchmark @end code_aux def=gfInverse

def Reedsolo.gfInverse : Reedsolo.GfInverseSig :=
-- !benchmark @start code def=gfInverse
  fun a => gfPowSq 8 a 254
-- !benchmark @end code def=gfInverse

-- ════════════════════════════════════════════════════════════════
-- rsGeneratorPoly
-- ════════════════════════════════════════════════════════════════

-- !benchmark @start code_aux def=rsGeneratorPoly
/-- The GF(2⁸) product of two polynomials (highest-degree-first coefficient
    lists). -/
def gfPolyMul (p q : List Nat) : List Nat :=
  let lp := p.length; let lq := q.length
  if lp == 0 || lq == 0 then []
  else (List.range (lp + lq - 1)).map (fun k =>
    (List.range lp).foldl (fun acc i =>
      let j := k - i
      if i ≤ k && j < lq then acc ^^^ Reedsolo.gfMul (p.getD i 0) (q.getD j 0) else acc) 0)
-- !benchmark @end code_aux def=rsGeneratorPoly

def Reedsolo.rsGeneratorPoly : Reedsolo.RsGeneratorPolySig :=
-- !benchmark @start code def=rsGeneratorPoly
  fun nsym => (List.range nsym).foldl (fun g i => gfPolyMul g [1, Reedsolo.gfPow alpha i]) [1]
-- !benchmark @end code def=rsGeneratorPoly

-- ════════════════════════════════════════════════════════════════
-- rsEncodeMsg
-- ════════════════════════════════════════════════════════════════

-- !benchmark @start code_aux def=rsEncodeMsg
def polyDivStep (divisor : List Nat) (msgout : List Nat) (i : Nat) : List Nat :=
  let coef := msgout.getD i 0
  if coef == 0 then msgout
  else (List.range divisor.length).foldl (fun m j =>
    if j == 0 then m
    else m.set (i + j) ((m.getD (i+j) 0) ^^^ Reedsolo.gfMul (divisor.getD j 0) coef)) msgout

/-- The polynomial remainder of `dividend` modulo a monic `divisor`. -/
def polyMod (dividend divisor : List Nat) : List Nat :=
  let sep := divisor.length - 1
  let n := dividend.length - sep
  let final := (List.range n).foldl (fun m i => polyDivStep divisor m i) dividend
  final.drop (final.length - sep)
-- !benchmark @end code_aux def=rsEncodeMsg

def Reedsolo.rsEncodeMsg : Reedsolo.RsEncodeMsgSig :=
-- !benchmark @start code def=rsEncodeMsg
  fun msg nsym =>
    let gen := Reedsolo.rsGeneratorPoly nsym
    let dividend := msg ++ List.replicate nsym 0
    msg ++ polyMod dividend gen
-- !benchmark @end code def=rsEncodeMsg
