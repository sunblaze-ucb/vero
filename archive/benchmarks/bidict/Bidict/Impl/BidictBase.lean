-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Bidict.Impl.BidictBase

Core bidirectional mapping type and operations. `BidictBase KT VT` is an
ordered association list preserving insertion order, enabling both
bidirectional lookup and ordered iteration. The `inverse` / `inv` operations
swap key and value roles; `union` / `runion` merge two bidicts with left- and
right-biased semantics respectively.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Core types (DO NOT MODIFY) ────────────────────────────────

/-- Ordered association list used as the backing store for bidicts.
    Preserves insertion order; keys are unique by convention. -/
abbrev BidictBase (KT VT : Type) := List (KT × VT)

/-- Association-list "HashMap" used in test-case constructors. -/
abbrev HashMap (KT VT : Type) := List (KT × VT)

/-- Build a `HashMap` from a literal list of pairs (identity). -/
def HashMap.ofList {KT VT : Type} (l : List (KT × VT)) : HashMap KT VT := l

/-- Wrap an association list as a `BidictBase`. -/
def Bidict.init {KT VT : Type} (m : HashMap KT VT) : BidictBase KT VT := m

variable {KT VT : Type} [BEq KT] [BEq VT] [Hashable KT] [Hashable VT]

namespace Bidict

-- ── API signatures (DO NOT MODIFY) ───────────────────────────
-- Note: sigs are polymorphic abbrevs; concrete functions use explicit params.

abbrev InverseSig  := BidictBase KT VT → BidictBase VT KT
abbrev InvSig      := BidictBase KT VT → BidictBase VT KT
abbrev CopySig     := BidictBase KT VT → BidictBase KT VT
abbrev UnionSig    := BidictBase KT VT → BidictBase KT VT → BidictBase KT VT
abbrev RunionSig   := BidictBase KT VT → BidictBase KT VT → BidictBase KT VT
abbrev LengthSig   := BidictBase KT VT → Nat
abbrev IterSig     := BidictBase KT VT → List KT
abbrev GetitemSig  := BidictBase KT VT → KT → Option VT

end Bidict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── inverse ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=inverse
-- !benchmark @end code_aux def=inverse

def Bidict.inverse (self : BidictBase KT VT) : BidictBase VT KT :=
-- !benchmark @start code def=inverse
  self.map (fun (k, v) => (v, k))
-- !benchmark @end code def=inverse

-- ── inv ──────────────────────────────────────────────────────

-- !benchmark @start code_aux def=inv
-- !benchmark @end code_aux def=inv

def Bidict.inv (self : BidictBase KT VT) : BidictBase VT KT :=
-- !benchmark @start code def=inv
  Bidict.inverse self
-- !benchmark @end code def=inv


-- ── copy ─────────────────────────────────────────────────────

-- !benchmark @start code_aux def=copy
-- !benchmark @end code_aux def=copy

def Bidict.copy (self : BidictBase KT VT) : BidictBase KT VT :=
-- !benchmark @start code def=copy
  self
-- !benchmark @end code def=copy

-- ── union ────────────────────────────────────────────────────

-- !benchmark @start code_aux def=union
-- !benchmark @end code_aux def=union

def Bidict.union (self other : BidictBase KT VT) : BidictBase KT VT :=
-- !benchmark @start code def=union
  self ++ (other.filter (fun (k, _) => !self.any (fun (k', _) => k' == k)))
-- !benchmark @end code def=union

-- ── runion ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=runion
-- !benchmark @end code_aux def=runion

def Bidict.runion (self other : BidictBase KT VT) : BidictBase KT VT :=
-- !benchmark @start code def=runion
  -- Keep self's order; take other's value on key conflict; append other's new pairs.
  let updated := self.map (fun (k, v) =>
    match other.find? (fun (k', _) => k' == k) with
    | some (_, v') => (k, v')
    | none         => (k, v))
  let newEntries := other.filter (fun (k, _) => !self.any (fun (k', _) => k' == k))
  updated ++ newEntries
-- !benchmark @end code def=runion

-- ── length ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=length
-- !benchmark @end code_aux def=length

def Bidict.length (self : BidictBase KT VT) : Nat :=
-- !benchmark @start code def=length
  self.length
-- !benchmark @end code def=length

-- ── iter ─────────────────────────────────────────────────────

-- !benchmark @start code_aux def=iter
-- !benchmark @end code_aux def=iter

def Bidict.iter (self : BidictBase KT VT) : List KT :=
-- !benchmark @start code def=iter
  self.map Prod.fst
-- !benchmark @end code def=iter

-- ── getitem ──────────────────────────────────────────────────

-- !benchmark @start code_aux def=getitem
-- !benchmark @end code_aux def=getitem

def Bidict.getitem (self : BidictBase KT VT) (key : KT) : Option VT :=
-- !benchmark @start code def=getitem
  (self.find? (fun (k, _) => k == key)).map Prod.snd
-- !benchmark @end code def=getitem
