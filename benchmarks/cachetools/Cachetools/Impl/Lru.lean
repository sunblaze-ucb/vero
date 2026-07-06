-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Cachetools.Impl.Lru

A fixed-capacity least-recently-used (LRU) cache over keys. Values are
abstracted away; the cache is the list of keys currently present, ordered
MOST-RECENTLY-USED FIRST (head = MRU, last = LRU, the next eviction
victim). Keys are `Nat`.

API: `empty`, `contains`, `get` (touch a key), `put` (insert/update), and
`lruKey` (report the eviction victim). Recency is the observable state the
specs pin; behaviour is defined in `Spec/Lru.lean`.

Types and signatures are fixed vocabulary (DO NOT MODIFY).
-/

-- ── Core data types (DO NOT MODIFY) ──────────────────────────

/-- An LRU cache: a fixed `capacity` and the list of keys currently
    present, MOST-RECENTLY-USED FIRST (head = MRU, last = LRU). Keys are
    deduplicated; `order.length ≤ capacity` is maintained. -/
structure Lru where
  capacity : Nat
  order    : List Nat
deriving Repr, DecidableEq

namespace Cachetools

-- ── API signatures (DO NOT MODIFY) ───────────────────────────

/-- `empty cap`: a fresh empty cache with the given capacity. -/
abbrev EmptySig    := Nat → Lru

/-- `contains c k`: whether key `k` is currently present in the cache. -/
abbrev ContainsSig := Lru → Nat → Bool

/-- `get c k`: touch key `k`. On a hit, `k` becomes the MRU and the updated
    cache is returned; on a miss the cache is returned unchanged (a `get`
    never inserts). -/
abbrev GetSig      := Lru → Nat → Lru

/-- `put c k`: insert or update key `k`, making it the MRU. If this brings
    the cache over its capacity, the LRU key is evicted. -/
abbrev PutSig      := Lru → Nat → Lru

/-- `lruKey c`: the current eviction victim — the least-recently-used key,
    or `none` if the cache is empty. -/
abbrev LruKeySig   := Lru → Option Nat

end Cachetools

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=empty
-- !benchmark @end code_aux def=empty

def Cachetools.empty : Cachetools.EmptySig :=
-- !benchmark @start code def=empty
  fun cap => { capacity := cap, order := [] }
-- !benchmark @end code def=empty

-- !benchmark @start code_aux def=contains
-- !benchmark @end code_aux def=contains

def Cachetools.contains : Cachetools.ContainsSig :=
-- !benchmark @start code def=contains
  fun c k => c.order.contains k
-- !benchmark @end code def=contains

-- !benchmark @start code_aux def=get
-- !benchmark @end code_aux def=get

def Cachetools.get : Cachetools.GetSig :=
-- !benchmark @start code def=get
  fun c k =>
    if c.order.contains k then
      { capacity := c.capacity, order := k :: c.order.filter (fun j => !(j == k)) }
    else
      c
-- !benchmark @end code def=get

-- !benchmark @start code_aux def=put
-- !benchmark @end code_aux def=put

def Cachetools.put : Cachetools.PutSig :=
-- !benchmark @start code def=put
  fun c k =>
    let moved := k :: c.order.filter (fun j => !(j == k))
    let trimmed := if moved.length > c.capacity then moved.dropLast else moved
    { capacity := c.capacity, order := trimmed }
-- !benchmark @end code def=put

-- !benchmark @start code_aux def=lruKey
-- !benchmark @end code_aux def=lruKey

def Cachetools.lruKey : Cachetools.LruKeySig :=
-- !benchmark @start code def=lruKey
  fun c => c.order.getLast?
-- !benchmark @end code def=lruKey
