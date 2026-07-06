-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Json.Impl.Utils.Vectors

Vector vocabulary and reference implementations translated from
`JSON.Utils.Vectors`.

DO NOT MODIFY types or signatures - these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace JSON

-- Types (no markers - fixed vocabulary)

inductive VectorError where
  | outOfMemory
  deriving Repr, DecidableEq, BEq

structure JVector (α : Type) where
  items : List α
  capacity : Nat
  default_ : α

-- Spec helpers (no markers - fixed vocabulary)

def maxCapacityU32 : Nat := 2 ^ 32 - 1

def maxCapacityBeforeDoubling : Nat := (2 ^ 32 - 1) / 2

def defaultNewCapacity (capacity : UInt32) : UInt32 :=
  if capacity.toNat < maxCapacityBeforeDoubling then
    UInt32.ofNat (2 * capacity.toNat)
  else
    UInt32.ofNat maxCapacityU32

def vector__Valid? {α : Type} (v : JVector α) : Prop :=
  v.capacity ≠ 0 ∧ v.items.length ≤ v.capacity

-- API signatures (no markers - fixed vocabulary)

abbrev VectorPutSig := ∀ {α : Type}, JVector α → UInt32 → α → JVector α

abbrev VectorReallocSig := ∀ {α : Type}, JVector α → UInt32 → Except VectorError (JVector α)

abbrev VectorPopFastSig := ∀ {α : Type}, JVector α → JVector α

abbrev VectorPushFastSig := ∀ {α : Type}, JVector α → α → JVector α

abbrev VectorReallocDefaultSig := ∀ {α : Type}, JVector α → Except VectorError (JVector α)

abbrev VectorEnsureSig := ∀ {α : Type}, JVector α → UInt32 → Except VectorError (JVector α)

abbrev VectorPushSig := ∀ {α : Type}, JVector α → α → Except VectorError (JVector α)

end JSON

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=vector_Put
-- !benchmark @end code_aux def=vector_Put

def JSON.vector_Put : JSON.VectorPutSig :=
-- !benchmark @start code def=vector_Put
  fun {α : Type} (v : JSON.JVector α) (idx : UInt32) (a : α) =>
    { v with items := v.items.set idx.toNat a }
-- !benchmark @end code def=vector_Put

-- !benchmark @start code_aux def=vector_Realloc
-- !benchmark @end code_aux def=vector_Realloc

def JSON.vector_Realloc : JSON.VectorReallocSig :=
-- !benchmark @start code def=vector_Realloc
  fun {α : Type} (v : JSON.JVector α) (newCapacity : UInt32) =>
    if v.capacity < newCapacity.toNat then
      .ok { v with capacity := newCapacity.toNat }
    else
      .ok v
-- !benchmark @end code def=vector_Realloc

-- !benchmark @start code_aux def=vector_PopFast
-- !benchmark @end code_aux def=vector_PopFast

def JSON.vector_PopFast : JSON.VectorPopFastSig :=
-- !benchmark @start code def=vector_PopFast
  fun {α : Type} (v : JSON.JVector α) =>
    { v with items := v.items.dropLast }
-- !benchmark @end code def=vector_PopFast

-- !benchmark @start code_aux def=vector_PushFast
-- !benchmark @end code_aux def=vector_PushFast

def JSON.vector_PushFast : JSON.VectorPushFastSig :=
-- !benchmark @start code def=vector_PushFast
  fun {α : Type} (v : JSON.JVector α) (a : α) =>
    { v with items := v.items ++ [a] }
-- !benchmark @end code def=vector_PushFast

-- !benchmark @start code_aux def=vector_ReallocDefault
-- !benchmark @end code_aux def=vector_ReallocDefault

def JSON.vector_ReallocDefault : JSON.VectorReallocDefaultSig :=
-- !benchmark @start code def=vector_ReallocDefault
  fun {α : Type} (v : JSON.JVector α) =>
    if v.capacity = JSON.maxCapacityU32 then
      .error .outOfMemory
    else
      let newCapacity :=
        if v.capacity = 0 then
          1
        else if v.capacity < JSON.maxCapacityBeforeDoubling then
          2 * v.capacity
        else if v.capacity < JSON.maxCapacityU32 then
          JSON.maxCapacityU32
        else
          v.capacity + 1
      .ok { v with capacity := newCapacity }
-- !benchmark @end code def=vector_ReallocDefault

-- !benchmark @start code_aux def=vector_Ensure
-- !benchmark @end code_aux def=vector_Ensure

def JSON.vector_Ensure : JSON.VectorEnsureSig :=
-- !benchmark @start code def=vector_Ensure
  fun {α : Type} (v : JSON.JVector α) (reserved : UInt32) =>
    let needed := v.items.length + reserved.toNat
    if needed > JSON.maxCapacityU32 then
      .error .outOfMemory
    else if needed ≤ v.capacity then
      .ok v
    else
      .ok { v with capacity := needed }
-- !benchmark @end code def=vector_Ensure

-- !benchmark @start code_aux def=vector_Push
-- !benchmark @end code_aux def=vector_Push

def JSON.vector_Push : JSON.VectorPushSig :=
-- !benchmark @start code def=vector_Push
  fun {α : Type} (v : JSON.JVector α) (a : α) =>
    if v.items.length < v.capacity then
      .ok (JSON.vector_PushFast v a)
    else if v.capacity = JSON.maxCapacityU32 then
      .error .outOfMemory
    else
      match JSON.vector_ReallocDefault v with
      | .ok v' => .ok (JSON.vector_PushFast v' a)
      | .error err => .error err
-- !benchmark @end code def=vector_Push
