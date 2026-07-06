import Bidict.Impl.BidictBase

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Bidict.Impl.OrderedBidict

Ordered bidictional mapping preserving insertion order. `OrderedBidict KT VT`
wraps a `BidictBase KT VT` (an insertion-ordered association list) and exposes
ordered iteration, in-place reordering (`moveToEnd`), and ordered pop
operations.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────────

/-- Ordered bidictional mapping: backs every operation with an insertion-ordered
    association list so that iteration order equals insertion order. -/
structure OrderedBidict (KT VT : Type) where
  data : BidictBase KT VT

/-- Structural equality for `OrderedBidict`. -/
instance {KT VT : Type} [BEq KT] [BEq VT] :
    BEq (OrderedBidict KT VT) where
  beq a b := a.data == b.data

variable {KT VT : Type} [BEq KT] [BEq VT] [Hashable KT] [Hashable VT]

namespace Bidict

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

abbrev InitOrderedBidictSig :=
  BidictBase KT VT → OrderedBidict KT VT
abbrev IterOrderedBidictSig :=
  OrderedBidict KT VT → Bool → List KT
abbrev InverseOrderedBidictSig :=
  OrderedBidict KT VT → OrderedBidict VT KT
abbrev InvOrderedBidictSig :=
  OrderedBidict KT VT → OrderedBidict VT KT
abbrev ClearOrderedBidictSig :=
  OrderedBidict KT VT → OrderedBidict KT VT
/-- `popOrderedBidict` returns `none` if key is absent (undefined in Python). -/
abbrev PopOrderedBidictSig :=
  OrderedBidict KT VT → KT → Option (OrderedBidict KT VT × VT)
/-- `popitemOrderedBidict` returns `none` if the bidict is empty. -/
abbrev PopitemOrderedBidictSig :=
  OrderedBidict KT VT → Bool → Option (OrderedBidict KT VT × (KT × VT))
abbrev MoveToEndOrderedBidictSig :=
  OrderedBidict KT VT → KT → Bool → OrderedBidict KT VT
abbrev KeysOrderedBidictSig :=
  OrderedBidict KT VT → List KT
abbrev ItemsOrderedBidictSig :=
  OrderedBidict KT VT → List (KT × VT)

end Bidict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── initOrderedBidict ─────────────────────────────────────────

-- !benchmark @start code_aux def=initOrderedBidict
-- !benchmark @end code_aux def=initOrderedBidict

def Bidict.initOrderedBidict (self : BidictBase KT VT) :
    OrderedBidict KT VT :=
-- !benchmark @start code def=initOrderedBidict
  { data := self }
-- !benchmark @end code def=initOrderedBidict

-- ── iterOrderedBidict ─────────────────────────────────────────

-- !benchmark @start code_aux def=iterOrderedBidict
-- !benchmark @end code_aux def=iterOrderedBidict

def Bidict.iterOrderedBidict (self : OrderedBidict KT VT) (reverse : Bool) :
    List KT :=
-- !benchmark @start code def=iterOrderedBidict
  let keys := self.data.map Prod.fst
  if reverse then keys.reverse else keys
-- !benchmark @end code def=iterOrderedBidict

-- ── inverseOrderedBidict ──────────────────────────────────────

-- !benchmark @start code_aux def=inverseOrderedBidict
-- !benchmark @end code_aux def=inverseOrderedBidict

def Bidict.inverseOrderedBidict (self : OrderedBidict KT VT) :
    OrderedBidict VT KT :=
-- !benchmark @start code def=inverseOrderedBidict
  { data := self.data.map (fun (k, v) => (v, k)) }
-- !benchmark @end code def=inverseOrderedBidict

-- ── invOrderedBidict ──────────────────────────────────────────

-- !benchmark @start code_aux def=invOrderedBidict
-- !benchmark @end code_aux def=invOrderedBidict

def Bidict.invOrderedBidict (self : OrderedBidict KT VT) :
    OrderedBidict VT KT :=
-- !benchmark @start code def=invOrderedBidict
  Bidict.inverseOrderedBidict self
-- !benchmark @end code def=invOrderedBidict

-- ── clearOrderedBidict ────────────────────────────────────────

-- !benchmark @start code_aux def=clearOrderedBidict
-- !benchmark @end code_aux def=clearOrderedBidict

def Bidict.clearOrderedBidict (self : OrderedBidict KT VT) :
    OrderedBidict KT VT :=
-- !benchmark @start code def=clearOrderedBidict
  { self with data := [] }
-- !benchmark @end code def=clearOrderedBidict

-- ── popOrderedBidict ──────────────────────────────────────────

-- !benchmark @start code_aux def=popOrderedBidict
-- !benchmark @end code_aux def=popOrderedBidict

def Bidict.popOrderedBidict (self : OrderedBidict KT VT) (key : KT) :
    Option (OrderedBidict KT VT × VT) :=
-- !benchmark @start code def=popOrderedBidict
  match self.data.find? (fun (k, _) => k == key) with
  | none        => none
  | some (_, v) =>
      let newData := self.data.filter (fun (k, _) => !(k == key))
      some ({ data := newData }, v)
-- !benchmark @end code def=popOrderedBidict

-- ── popitemOrderedBidict ──────────────────────────────────────

-- !benchmark @start code_aux def=popitemOrderedBidict
-- !benchmark @end code_aux def=popitemOrderedBidict

def Bidict.popitemOrderedBidict (self : OrderedBidict KT VT) (last : Bool) :
    Option (OrderedBidict KT VT × (KT × VT)) :=
-- !benchmark @start code def=popitemOrderedBidict
  if last then
    -- Remove the last entry.
    match self.data.getLast? with
    | none      => none
    | some item =>
        let newData := self.data.take (self.data.length - 1)
        some ({ data := newData }, item)
  else
    -- Remove the first entry.
    match self.data with
    | []           => none
    | item :: rest => some ({ data := rest }, item)
-- !benchmark @end code def=popitemOrderedBidict

-- ── moveToEndOrderedBidict ────────────────────────────────────

-- !benchmark @start code_aux def=moveToEndOrderedBidict
-- !benchmark @end code_aux def=moveToEndOrderedBidict

def Bidict.moveToEndOrderedBidict (self : OrderedBidict KT VT) (key : KT)
    (last : Bool) : OrderedBidict KT VT :=
-- !benchmark @start code def=moveToEndOrderedBidict
  match self.data.find? (fun (k, _) => k == key) with
  | none      => self  -- key absent; no-op
  | some item =>
      let rest := self.data.filter (fun (k, _) => !(k == key))
      if last then
        { data := rest ++ [item] }
      else
        { data := item :: rest }
-- !benchmark @end code def=moveToEndOrderedBidict

-- ── keysOrderedBidict ─────────────────────────────────────────

-- !benchmark @start code_aux def=keysOrderedBidict
-- !benchmark @end code_aux def=keysOrderedBidict

def Bidict.keysOrderedBidict (self : OrderedBidict KT VT) : List KT :=
-- !benchmark @start code def=keysOrderedBidict
  self.data.map Prod.fst
-- !benchmark @end code def=keysOrderedBidict

-- ── itemsOrderedBidict ────────────────────────────────────────

-- !benchmark @start code_aux def=itemsOrderedBidict
-- !benchmark @end code_aux def=itemsOrderedBidict

def Bidict.itemsOrderedBidict (self : OrderedBidict KT VT) :
    List (KT × VT) :=
-- !benchmark @start code def=itemsOrderedBidict
  self.data
-- !benchmark @end code def=itemsOrderedBidict
