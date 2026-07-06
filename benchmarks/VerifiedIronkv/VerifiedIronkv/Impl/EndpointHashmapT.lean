import VerifiedIronkv.Impl.HashmapT

/-!
# VerifiedIronkv.Impl.EndpointHashmapT

Translated Verus vocabulary and reference implementations for `EndpointHashmapT`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

structure HashMap (V : Type) where
  entries : List (AbstractEndPoint × V)
  deriving Repr, DecidableEq, BEq, Inhabited

def endpointHashmapTGet_spec {V : Type} [DecidableEq AbstractEndPoint] : List (AbstractEndPoint × V) → AbstractEndPoint → Option V
  | [], _ => none
  | (k, v) :: rest, key => if k = key then some v else endpointHashmapTGet_spec rest key

def endpointHashmapEntriesAreMapLike {V : Type} (entries : List (AbstractEndPoint × V)) : Prop :=
  List.Nodup (entries.map Prod.fst)

def endpointHashmapEntriesRepresentMap {V : Type} [DecidableEq AbstractEndPoint]
    (entries : List (AbstractEndPoint × V)) (ghostLookup : AbstractEndPoint → Option V) : Prop :=
  endpointHashmapEntriesAreMapLike entries ∧
  ∀ key, ghostLookup key = endpointHashmapTGet_spec entries key

def endpointHashmapMapListLookupBridge {V : Type} [DecidableEq AbstractEndPoint]
    (entries : List (AbstractEndPoint × V)) (ghostLookup : AbstractEndPoint → Option V) : Prop :=
  endpointHashmapEntriesRepresentMap entries ghostLookup

def endpointHashmapEntriesSet {V : Type} [DecidableEq AbstractEndPoint]
    (entries : List (AbstractEndPoint × V)) (key : AbstractEndPoint) (value : V) :
    List (AbstractEndPoint × V) :=
  (key, value) :: entries.filter (fun kv => if kv.1 = key then false else true)

def endpointHashmapGhostLookupEmpty {V : Type} : AbstractEndPoint → Option V :=
  fun _ => none

def endpointHashmapGhostLookupInsert {V : Type} [DecidableEq AbstractEndPoint]
    (oldLookup : AbstractEndPoint → Option V) (key : AbstractEndPoint) (value : V) :
    AbstractEndPoint → Option V :=
  fun k => if k = key then some value else oldLookup k

def endpointHashmapGhostLookupMapValues {V W : Type}
    (f : V → W) (lookup : AbstractEndPoint → Option V) :
    AbstractEndPoint → Option W :=
  fun k => Option.map f (lookup k)

def endpointHashmapEntriesMapValues {V W : Type}
    (f : V → W) (entries : List (AbstractEndPoint × V)) :
    List (AbstractEndPoint × W) :=
  entries.map (fun kv => (kv.1, f kv.2))

def endpointHashmapEntriesKeys {V : Type}
    (entries : List (AbstractEndPoint × V)) : List AbstractEndPoint :=
  entries.map Prod.fst

def endpointHashmapKeysDomainBridge {V : Type} [DecidableEq AbstractEndPoint]
    (entries : List (AbstractEndPoint × V)) (keys : List AbstractEndPoint) : Prop :=
  endpointHashmapEntriesAreMapLike entries ∧
  keys = endpointHashmapEntriesKeys entries ∧
  ∀ key, key ∈ keys ↔ ∃ value, endpointHashmapTGet_spec entries key = some value

def put_spec {V : Type} [DecidableEq AbstractEndPoint] (oldMap newMap : List (AbstractEndPoint × V)) (key : AbstractEndPoint) (value : V) : Prop :=
  endpointHashmapTGet_spec newMap key = some value ∧
  ∀ k, k ≠ key → endpointHashmapTGet_spec newMap k = endpointHashmapTGet_spec oldMap k

def swap_spec {V : Type} [DecidableEq AbstractEndPoint] (oldMap newMap : List (AbstractEndPoint × V)) (key : AbstractEndPoint) (inputValue outputValue defaultValue : V) : Prop :=
  outputValue = (endpointHashmapTGet_spec oldMap key).getD defaultValue ∧
  put_spec oldMap newMap key inputValue

def endpointHashmapNewEntriesBridge {V : Type} [DecidableEq AbstractEndPoint]
    (entries : List (AbstractEndPoint × V)) : Prop :=
  entries = [] ∧
  endpointHashmapEntriesRepresentMap entries (endpointHashmapGhostLookupEmpty (V := V))

def endpointHashmapInsertEntriesBridge {V : Type} [DecidableEq AbstractEndPoint]
    (oldEntries newEntries : List (AbstractEndPoint × V))
    (oldLookup : AbstractEndPoint → Option V)
    (key : AbstractEndPoint) (value : V) : Prop :=
  endpointHashmapEntriesRepresentMap oldEntries oldLookup →
  newEntries = endpointHashmapEntriesSet oldEntries key value →
    endpointHashmapEntriesRepresentMap newEntries
      (endpointHashmapGhostLookupInsert oldLookup key value) ∧
    put_spec oldEntries newEntries key value

def endpointHashmapPutEntriesBridge {V : Type} [DecidableEq AbstractEndPoint]
    (oldEntries newEntries : List (AbstractEndPoint × V))
    (oldLookup : AbstractEndPoint → Option V)
    (key : AbstractEndPoint) (value : V) : Prop :=
  endpointHashmapInsertEntriesBridge oldEntries newEntries oldLookup key value

def endpointHashmapSwapEntriesBridge {V : Type} [DecidableEq AbstractEndPoint]
    (oldEntries newEntries : List (AbstractEndPoint × V))
    (oldLookup : AbstractEndPoint → Option V)
    (key : AbstractEndPoint) (inputValue outputValue defaultValue : V) : Prop :=
  endpointHashmapEntriesRepresentMap oldEntries oldLookup →
  newEntries = endpointHashmapEntriesSet oldEntries key inputValue →
  outputValue = (oldLookup key).getD defaultValue →
    endpointHashmapEntriesRepresentMap newEntries
      (endpointHashmapGhostLookupInsert oldLookup key inputValue) ∧
    swap_spec oldEntries newEntries key inputValue outputValue defaultValue

def endpointHashmapMapValuesEntriesBridge {V W : Type} [DecidableEq AbstractEndPoint]
    (entries : List (AbstractEndPoint × V))
    (lookup : AbstractEndPoint → Option V) (f : V → W) : Prop :=
  endpointHashmapEntriesRepresentMap entries lookup →
    endpointHashmapEntriesRepresentMap
      (endpointHashmapEntriesMapValues f entries)
      (endpointHashmapGhostLookupMapValues f lookup)

namespace Bank


end Bank
