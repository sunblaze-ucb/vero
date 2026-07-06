import Bidict.Impl.BidictBase
import Bidict.Impl.Exc
import Bidict.Impl.OnDup

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Bidict.Impl.MutableBidict

Mutable bidictional mapping with a configurable on-duplication policy.
`MutableBidict KT VT` wraps a `BidictBase KT VT` together with an `OnDup`
value that governs how duplicate keys or values are handled on insertion.
All mutating operations return a new `MutableBidict` (functional style).

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

-- ── Types (DO NOT MODIFY) ─────────────────────────────────────

/-- Mutable bidictional mapping: association-list data plus an on-duplication
    policy.  All "mutation" returns a fresh `MutableBidict`. -/
structure MutableBidict (KT VT : Type) where
  data  : BidictBase KT VT
  ondup : OnDup

/-- Structural equality for `MutableBidict`: compare data and policy. -/
instance {KT VT : Type} [BEq KT] [BEq VT] :
    BEq (MutableBidict KT VT) where
  beq a b := a.data == b.data && a.ondup == b.ondup

variable {KT VT : Type} [BEq KT] [BEq VT] [Hashable KT] [Hashable VT]

namespace Bidict

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

abbrev InitMutableBidictSig :=
  BidictBase KT VT → OnDup → MutableBidict KT VT
abbrev DelItemSig :=
  MutableBidict KT VT → KT → MutableBidict KT VT
abbrev SetItemSig :=
  MutableBidict KT VT → KT → VT →
    Except DuplicationError (MutableBidict KT VT)
abbrev ForceputSig :=
  MutableBidict KT VT → KT → VT → MutableBidict KT VT
abbrev ClearSig :=
  MutableBidict KT VT → MutableBidict KT VT
abbrev PopSig :=
  ∀ {DT : Type}, MutableBidict KT VT → KT → DT →
    MutableBidict KT VT × Sum VT DT
/-- `popitem` returns `none` when the bidict is empty (undefined in Python). -/
abbrev PopitemSig :=
  MutableBidict KT VT → Option (MutableBidict KT VT × (KT × VT))
abbrev UpdateSig :=
  MutableBidict KT VT → BidictBase KT VT →
    Except DuplicationError (MutableBidict KT VT)
abbrev ForceupdateSig :=
  MutableBidict KT VT → BidictBase KT VT → MutableBidict KT VT
abbrev PutallSig :=
  MutableBidict KT VT → BidictBase KT VT → OnDup → MutableBidict KT VT

end Bidict

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- ── initMutableBidict ─────────────────────────────────────────

-- !benchmark @start code_aux def=initMutableBidict
-- !benchmark @end code_aux def=initMutableBidict

def Bidict.initMutableBidict (self : BidictBase KT VT) (ondup : OnDup) :
    MutableBidict KT VT :=
-- !benchmark @start code def=initMutableBidict
  { data := self, ondup := ondup }
-- !benchmark @end code def=initMutableBidict

-- ── delItem ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=delItem
-- !benchmark @end code_aux def=delItem

def Bidict.delItem (self : MutableBidict KT VT) (key : KT) :
    MutableBidict KT VT :=
-- !benchmark @start code def=delItem
  { self with data := self.data.filter (fun (k, _) => !(k == key)) }
-- !benchmark @end code def=delItem

-- ── setItem ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=setItem
-- !benchmark @end code_aux def=setItem

--   actual constructor is DuplicationError.duplicateKeyError; those #guard
--   tests are wrapped in @review in Test.lean.
def Bidict.setItem (self : MutableBidict KT VT) (key : KT) (val : VT) :
    Except DuplicationError (MutableBidict KT VT) :=
-- !benchmark @start code def=setItem
  let kExists := self.data.any (fun (k, _) => k == key)
  let vExists := self.data.any (fun (_, v) => v == val)
  -- Phase 1: key conflict
  match kExists, self.ondup.key with
  | true,  OnDupAction.raise   => Except.error DuplicationError.duplicateKeyError
  | true,  OnDupAction.dropNew => Except.ok self
  | _, _ =>
    -- Phase 2: value conflict
    match vExists, self.ondup.val with
    | true,  OnDupAction.raise   => Except.error DuplicationError.duplicateValueError
    | true,  OnDupAction.dropNew => Except.ok self
    | _, _ =>
      -- Phase 3: remove stale entries then append new pair
      let d0 := match kExists, self.ondup.key with
        | true, OnDupAction.dropOld =>
            self.data.filter (fun (k, _) => !(k == key))
        | _, _ => self.data
      let d1 := match vExists, self.ondup.val with
        | true, OnDupAction.dropOld =>
            d0.filter (fun (_, v) => !(v == val))
        | _, _ => d0
      Except.ok { self with data := d1 ++ [(key, val)] }
-- !benchmark @end code def=setItem

-- ── forceput ──────────────────────────────────────────────────

-- !benchmark @start code_aux def=forceput
-- !benchmark @end code_aux def=forceput

def Bidict.forceput (self : MutableBidict KT VT) (key : KT) (val : VT) :
    MutableBidict KT VT :=
-- !benchmark @start code def=forceput
  let kExists := self.data.any (fun (k, _) => k == key)
  if kExists then
    -- Update value in-place; also drop any other entry carrying val.
    let cleaned := self.data.filter (fun (k, v) => k == key || !(v == val))
    { self with data :=
        cleaned.map (fun (k, v) => if k == key then (k, val) else (k, v)) }
  else
    -- Remove any entry with the new value, then append.
    let cleaned := self.data.filter (fun (_, v) => !(v == val))
    { self with data := cleaned ++ [(key, val)] }
-- !benchmark @end code def=forceput

-- ── clear ─────────────────────────────────────────────────────

-- !benchmark @start code_aux def=clear
-- !benchmark @end code_aux def=clear

def Bidict.clear (self : MutableBidict KT VT) : MutableBidict KT VT :=
-- !benchmark @start code def=clear
  { self with data := [] }
-- !benchmark @end code def=clear

-- ── pop ───────────────────────────────────────────────────────

-- !benchmark @start code_aux def=pop
-- !benchmark @end code_aux def=pop

def Bidict.pop {DT : Type} (self : MutableBidict KT VT) (key : KT)
    (default : DT) : MutableBidict KT VT × Sum VT DT :=
-- !benchmark @start code def=pop
  match self.data.find? (fun (k, _) => k == key) with
  | some (_, v) =>
      ({ self with data := self.data.filter (fun (k, _) => !(k == key)) },
       Sum.inl v)
  | none =>
      (self, Sum.inr default)
-- !benchmark @end code def=pop

-- ── popitem ───────────────────────────────────────────────────

-- !benchmark @start code_aux def=popitem
-- !benchmark @end code_aux def=popitem

--   Benchmark signature says ST s (Prod KT VT); test #guards use `some`.
def Bidict.popitem (self : MutableBidict KT VT) :
    Option (MutableBidict KT VT × (KT × VT)) :=
-- !benchmark @start code def=popitem
  match self.data with
  | []           => none
  | item :: rest => some ({ self with data := rest }, item)
-- !benchmark @end code def=popitem

-- ── update ────────────────────────────────────────────────────

-- !benchmark @start code_aux def=update
-- !benchmark @end code_aux def=update

def Bidict.update (self : MutableBidict KT VT) (other : BidictBase KT VT) :
    Except DuplicationError (MutableBidict KT VT) :=
-- !benchmark @start code def=update
  other.foldl (fun acc (k, v) =>
    match acc with
    | Except.error e => Except.error e
    | Except.ok mb   =>
        match Bidict.setItem mb k v with
        | Except.ok mb'  => Except.ok mb'
        | Except.error e => Except.error e
  ) (Except.ok self)
-- !benchmark @end code def=update

-- ── forceupdate ───────────────────────────────────────────────

-- !benchmark @start code_aux def=forceupdate
-- !benchmark @end code_aux def=forceupdate

def Bidict.forceupdate (self : MutableBidict KT VT) (other : BidictBase KT VT) :
    MutableBidict KT VT :=
-- !benchmark @start code def=forceupdate
  other.foldl (fun acc (k, v) => Bidict.forceput acc k v) self
-- !benchmark @end code def=forceupdate

-- ── putall ────────────────────────────────────────────────────

-- !benchmark @start code_aux def=putall
-- !benchmark @end code_aux def=putall

def Bidict.putall (self : MutableBidict KT VT) (other : BidictBase KT VT)
    (mergeOndup : OnDup) : MutableBidict KT VT :=
-- !benchmark @start code def=putall
  -- Temporarily switch to mergeOndup for the merge pass.
  let mb0 : MutableBidict KT VT := { data := self.data, ondup := mergeOndup }
  let result := other.foldl (fun acc (k, v) =>
    match Bidict.setItem acc k v with
    | Except.ok mb   => mb
    | Except.error _ => acc  -- skip conflicting entries per mergeOndup
  ) mb0
  -- Restore original ondup.
  { result with ondup := self.ondup }
-- !benchmark @end code def=putall
