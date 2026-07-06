import Cachetools.Harness

/-!
# Cachetools.Spec.Lru

Specifications for the LRU cache operations. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`; the API is always reached through
`impl.cachetools.<fn>`, never by calling the reference `Cachetools.<fn>`
directly.

The single-operation specs pin the deterministic final state of the LRU
policy, anchored on the frozen list observers `List.head?`,
`List.getLast?`, `List.contains`, and `List.length`: a touched/inserted
key becomes the MRU head, and a full-capacity `put` evicts exactly the LRU
key. Together these distinguish a genuine LRU from a FIFO or evict-MRU
policy.

The `spec_applyOps_*` / `spec_applyMixed_*` families characterize the
whole-trace behaviour over an arbitrary sequence of `put`s (resp.
interleaved `get`/`put`s): global invariants (capacity bound, `Nodup`) and
a closed-form final state (`lruModel` / `keyModel`) — the `cap`
most-recently-used distinct keys in recency order. Later families state
stack-distance / reuse laws, eviction-count and eviction-order laws,
two-run capacity comparisons, and forgetting/saturation laws.

DO NOT MODIFY — this file is frozen curator-given content.
-/

-- ── Frozen op-sequence vocabulary (DO NOT MODIFY) ─────────────
-- These helpers reference only frozen list operations and the API
-- *function* passed in as an argument; they never mention `impl`
-- directly, so they are safe to share across the `spec_applyOps_*`
-- obligations. `applyOps` takes the `put` function explicitly and is
-- always instantiated at `impl.cachetools.put` inside the specs.

/-- Replay a sequence of insertions (a list of keys, oldest first) over a
    cache by folding the supplied single-step operation `step`. `step` is
    always instantiated at `impl.cachetools.put` inside the specs. -/
def applyOps (step : Lru → Nat → Lru) (c : Lru) (ops : List Nat) : Lru :=
  ops.foldl step c

/-- Deduplicate a list keeping the *first* occurrence of each key. Reading a
    recency order most-recently-used first, this keeps the most recent touch
    of each key. -/
def dedupKeepFirst : List Nat → List Nat
  | [] => []
  | x :: xs => x :: (dedupKeepFirst xs).filter (fun j => !(j == x))

/-- The closed-form LRU contents (recency order, MRU first) of a cache of
    capacity `cap` after replaying the put-trace `ops` from empty: the `cap`
    most-recent distinct keys, most-recently-put first. The canonical
    specification of what an LRU cache holds after a whole sequence. -/
def lruModel (cap : Nat) (ops : List Nat) : List Nat :=
  (dedupKeepFirst ops.reverse).take cap

-- ── Frozen MIXED op-sequence vocabulary (DO NOT MODIFY) ───────
-- The `spec_applyMixed_*` obligations quantify over an *interleaved* trace
-- of `get` AND `put` operations. As with `applyOps`, these helpers never
-- mention `impl` — `applyMixed` takes the `get` and `put` functions
-- explicitly and is always instantiated at `impl.cachetools.get` /
-- `impl.cachetools.put` inside the specs.

/-- A single mixed cache operation: either touch (a `get`, constructor
    `touch`) or insert (a `put`, constructor `store`) a key. The frozen
    alphabet for interleaved op-sequence obligations. The constructors are
    named `touch`/`store` (rather than `get`/`put`) so the frozen vocabulary
    never lexically shadows the scored API names. -/
inductive Op where
  | touch : Nat → Op
  | store : Nat → Op
deriving Repr, DecidableEq

/-- Apply one mixed operation, dispatching to the supplied `getf`/`putf`.
    Instantiated at `impl.cachetools.get` / `impl.cachetools.put`. -/
def stepMixed (getf putf : Lru → Nat → Lru) (c : Lru) : Op → Lru
  | Op.touch k => getf c k
  | Op.store k => putf c k

/-- Replay an interleaved `get`/`put` trace (oldest first) by folding the
    single-step dispatcher. -/
def applyMixed (getf putf : Lru → Nat → Lru) (c : Lru) (ops : List Op) : Lru :=
  ops.foldl (stepMixed getf putf) c

/-- One step of the closed-form recency model on a key list (MRU first) at
    capacity `cap`, mirroring the policy: a `get` of a present key makes it
    the MRU (no-op on a miss); a `put` makes `k` the MRU and evicts the LRU
    key on overflow. The reference single-step transition. -/
def keyStep (cap : Nat) (cur : List Nat) : Op → List Nat
  | Op.touch k => if cur.elem k then k :: cur.filter (fun j => !(j == k)) else cur
  | Op.store k =>
      let moved := k :: cur.filter (fun j => !(j == k))
      if moved.length > cap then moved.dropLast else moved

/-- The closed-form recency contents (MRU first) of a capacity-`cap` cache
    after replaying the interleaved `get`/`put` trace `ops` from empty: the
    `cap` most-recently-*touched* (got-while-present or put) distinct keys,
    in most-recently-touched-first order. The canonical specification of what
    the cache holds after a mixed sequence. -/
def keyModel (cap : Nat) (ops : List Op) : List Nat :=
  ops.foldl (keyStep cap) []

/-- Whether a mixed operation is a `get`. -/
def Op.isGet : Op → Bool
  | Op.touch _ => true
  | Op.store _ => false

/-- The prefix of a key list strictly before the first occurrence of `x`
    (all of it if `x` is absent). Over a *reversed* put-trace this collects
    the keys touched more recently than `x`'s most recent put. -/
def takeBefore (x : Nat) : List Nat → List Nat
  | [] => []
  | a :: as => if a == x then [] else a :: takeBefore x as

-- ── put: read-after-write and recency ─────────────────────────

/-- Read-after-write: after `put c k` (with positive capacity), `k` is
    present. -/
def spec_put_contains (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    c.capacity > 0 →
    impl.cachetools.contains (impl.cachetools.put c k) k = true

/-- Recency: after `put c k` (positive capacity), `k` is the
    most-recently-used key — the head of `order`. -/
def spec_put_mru (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    c.capacity > 0 →
    (impl.cachetools.put c k).order.head? = some k

-- ── get: hit moves to front, miss is a no-op ──────────────────

/-- A `get` hit moves the touched key to the front (it becomes the MRU). -/
def spec_get_hit_mru (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    impl.cachetools.contains c k = true →
    (impl.cachetools.get c k).order.head? = some k

/-- A `get` miss leaves the cache unchanged (no insertion). -/
def spec_get_miss_noop (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    impl.cachetools.contains c k = false →
    impl.cachetools.get c k = c

/-- A `get` preserves the presence of every other key: touching `k` may
    change its recency but never adds or drops any key `j ≠ k`. -/
def spec_get_preserves_keys (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k j : Nat), j ≠ k →
    impl.cachetools.contains (impl.cachetools.get c k) j = impl.cachetools.contains c j

-- ── eviction: the victim is the least-recently-used key ───────

/-- Minimality of eviction: a `put` of an absent key into a full-capacity
    cache changes membership in *exactly* one way per pre-existing key — for
    every key `j` other than the inserted `k`, `j` is present afterwards iff
    it was present before *and* it is not the LRU victim (the last element of
    `order`). Equivalently: the LRU key is the unique evicted key and every
    other present key survives.

    No positive-capacity hypothesis is needed — at capacity `0` a full cache
    has empty `order`, so the obligation is vacuous. The `Nodup` hypothesis
    records the standing cache invariant that keys are distinct. -/
def spec_evict_lru (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    c.order.length = c.capacity →
    impl.cachetools.contains c k = false →
    ∀ (victim : Nat), c.order.getLast? = some victim →
      c.order.Nodup →
      let c' := impl.cachetools.put c k
      ∀ (j : Nat), j ≠ k →
        impl.cachetools.contains c' j
          = (impl.cachetools.contains c j && !(j == victim))

-- ── structural invariants ─────────────────────────────────────

/-- `put` preserves the capacity field. -/
def spec_capacity_preserved (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    (impl.cachetools.put c k).capacity = c.capacity

/-- `put` maintains the size bound: if the cache was within capacity, it
    remains within capacity afterwards (an over-capacity insert evicts). -/
def spec_size_le_cap (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    c.order.length ≤ c.capacity →
    (impl.cachetools.put c k).order.length ≤ c.capacity

/-- `lruKey` reports the eviction victim: the last element of `order`. -/
def spec_lruKey_last (impl : RepoImpl) : Prop :=
  ∀ (c : Lru),
    impl.cachetools.lruKey c = c.order.getLast?

-- ── empty: the fresh-cache defining equations and boundaries ───

/-- A fresh cache holds no keys: `contains (empty cap) k` is always
    `false`. (Boundary / defining equation for `empty`.) -/
def spec_empty_contains (impl : RepoImpl) : Prop :=
  ∀ (cap k : Nat),
    impl.cachetools.contains (impl.cachetools.empty cap) k = false

/-- `empty cap` records exactly the requested capacity. -/
def spec_empty_capacity (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat),
    (impl.cachetools.empty cap).capacity = cap

/-- `empty cap` starts with an empty recency order. -/
def spec_empty_order (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat),
    (impl.cachetools.empty cap).order = []

/-- A fresh cache has no eviction victim: `lruKey (empty cap) = none`.
    (Boundary case linking `empty` and `lruKey`.) -/
def spec_empty_lruKey (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat),
    impl.cachetools.lruKey (impl.cachetools.empty cap) = none

-- ── contains: membership characterization, get consistency ─────

/-- `contains` decides recency-order membership: it is `true` exactly
    when `k` occurs in `order`. (Bidirectional characterization of the
    `contains` observer.) -/
def spec_contains_iff_mem (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    impl.cachetools.contains c k = true ↔ k ∈ c.order

/-- A `get` on a present key pins the whole resulting recency order to
    `k :: c.order.filter (· ≠ k)`: `k` at the front, every other key kept in
    its original relative order, nothing added or dropped. -/
def spec_get_keeps_present (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    impl.cachetools.contains c k = true →
    (impl.cachetools.get c k).order = k :: c.order.filter (fun j => !(j == k))

-- ── put: structural invariants and size relations ─────────────

/-- `put` preserves the standing `Nodup` invariant: if no key occurs twice
    before the insert, none does after. A single insertion never causes the
    cache to hold a duplicate key. -/
def spec_put_preserves_nodup (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    c.order.Nodup →
    (impl.cachetools.put c k).order.Nodup

/-- Updating an already-present key does not change the cache size: a `put`
    of a key already present leaves `order.length` unchanged. The `Nodup` and
    within-capacity hypotheses record the standing cache invariants. -/
def spec_put_existing_size (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    impl.cachetools.contains c k = true →
    c.order.length ≤ c.capacity →
    c.order.Nodup →
    (impl.cachetools.put c k).order.length = c.order.length

/-- Inserting a genuinely new key while strictly below capacity prepends it
    verbatim: the new recency order is exactly `k :: c.order` — no eviction
    is triggered and nothing is reordered. -/
def spec_put_new_grows (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    impl.cachetools.contains c k = false →
    c.order.length < c.capacity →
    (impl.cachetools.put c k).order = k :: c.order

/-- `put` is idempotent: re-inserting the same key immediately is a whole-
    state no-op, for *every* capacity (including the degenerate zero-capacity
    cache), provided the cache was within capacity. The within-capacity
    hypothesis records the standing size invariant. -/
def spec_put_idempotent (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    c.order.length ≤ c.capacity →
    impl.cachetools.put (impl.cachetools.put c k) k = impl.cachetools.put c k

-- ── get: structural invariants and idempotence ────────────────

/-- A read never changes the cache size: `get c k` leaves `order.length`
    unchanged. The `Nodup` hypothesis records the standing distinctness
    invariant. -/
def spec_get_preserves_size (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    c.order.Nodup →
    (impl.cachetools.get c k).order.length = c.order.length

/-- `get` preserves the capacity field. -/
def spec_get_preserves_capacity (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    (impl.cachetools.get c k).capacity = c.capacity

/-- `get` is idempotent: touching the same key twice in a row equals
    touching it once (the second touch finds it already at the front).
    Holds unconditionally — on a miss the first `get` is already the
    identity. Closure/idempotence law. -/
def spec_get_idempotent (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    impl.cachetools.get (impl.cachetools.get c k) k = impl.cachetools.get c k

-- ── lruKey: emptiness, membership, and the eviction tie ───────

/-- `lruKey` is `none` exactly when the cache is empty. (Bidirectional
    boundary characterization of the eviction-victim observer.) -/
def spec_lruKey_none_iff_empty (impl : RepoImpl) : Prop :=
  ∀ (c : Lru),
    impl.cachetools.lruKey c = none ↔ c.order = []

/-- The eviction victim, when it exists, is *exactly the last element* of
    the recency order — `c.order` splits as `c.order.dropLast ++ [victim]`. -/
def spec_lruKey_mem (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (victim : Nat),
    impl.cachetools.lruKey c = some victim →
    c.order = c.order.dropLast ++ [victim]

/-- Restatement of `spec_evict_lru` in terms of `lruKey`: a full-capacity
    `put` of an absent key changes membership in *exactly* one way per
    pre-existing key — for every key `j ≠ k`, `j` is present afterwards iff it
    was present before *and* it is not the key reported by `lruKey`.

    No positive-capacity hypothesis is needed (at capacity `0` a full cache is
    empty, so `lruKey` is `none` and the obligation is vacuous). The `Nodup`
    hypothesis is the standing cache invariant. -/
def spec_evict_victim_is_lruKey (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k victim : Nat),
    c.order.length = c.capacity →
    impl.cachetools.contains c k = false →
    c.order.Nodup →
    impl.cachetools.lruKey c = some victim →
    ∀ (j : Nat), j ≠ k →
      impl.cachetools.contains (impl.cachetools.put c k) j
        = (impl.cachetools.contains c j && !(j == victim))

-- ══ Whole-trace (op-sequence) obligations ═════════════════════
-- The specs below quantify over an arbitrary trace `ops : List Nat`
-- replayed through `impl.cachetools.put` via `applyOps`. They pin
-- global invariants and the closed-form final state of the policy over
-- the *entire* sequence, not a single step.

/-- Global invariant: replaying any trace of `put`s never changes the
    cache's `capacity` field — the declared capacity is fixed at creation and
    no sequence of insertions alters it. -/
def spec_applyOps_capacity (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (ops : List Nat),
    (applyOps impl.cachetools.put c ops).capacity = c.capacity

/-- Global invariant: the capacity bound is preserved over an arbitrary
    trace. If the cache starts within capacity, then after replaying any
    sequence of `put`s it is still within capacity — every over-capacity
    insert along the way evicts, so the cache never outgrows its declared
    size no matter how many keys are inserted. -/
def spec_applyOps_size_le_cap (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (ops : List Nat),
    c.order.length ≤ c.capacity →
    (applyOps impl.cachetools.put c ops).order.length ≤ c.capacity

/-- Global invariant: distinctness of keys is preserved over an arbitrary
    trace. From a cache whose keys are distinct, replaying any sequence of
    `put`s yields a cache whose keys are still distinct — an LRU cache never
    holds the same key twice, no matter how long the operation history. -/
def spec_applyOps_nodup (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (ops : List Nat),
    c.order.Nodup →
    (applyOps impl.cachetools.put c ops).order.Nodup

/-- Whole-trace characterization: replaying a put-trace `ops` from a fresh
    cache of capacity `cap` yields exactly the closed-form LRU contents
    `lruModel cap ops`. The full functional specification of the eviction
    policy over an entire operation sequence — precisely which keys survive
    and in what recency order after any number of insertions. -/
def spec_applyOps_contents (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat),
    (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order
      = lruModel cap ops

/-- Op-sequence final state: after replaying any trace into a positive-
    capacity cache, the most-recently-used key (head of `order`) is exactly
    the last key put (`ops.getLast?`). Recency is determined by the whole
    trace, not just the final shape. The empty-trace case is included — both
    sides are `none` — so no nonemptiness hypothesis is required; the head of
    the recency order tracks the final `put` for *every* trace. -/
def spec_applyOps_mru_is_last (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat),
    0 < cap →
    (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order.head?
      = ops.getLast?

/-- Membership over sequences: after replaying `ops` from empty, a key is
    present exactly when it is among the `cap` most-recent distinct puts,
    i.e. exactly when it occurs in `lruModel cap ops`. This is the
    whole-trace membership law — it simultaneously says recent keys
    survive and stale keys are gone. -/
def spec_applyOps_present_iff (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat) (k : Nat),
    impl.cachetools.contains
        (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops) k = true
      ↔ k ∈ lruModel cap ops

/-- Eviction over sequences: a key that is *not* among the `cap`
    most-recent distinct puts (not in `lruModel cap ops` — e.g. a key
    whose most recent put was followed by `cap` or more distinct other
    keys) has been evicted, and is absent after replaying the trace from
    empty. The eviction-count consequence of the contents formula. -/
def spec_applyOps_evicted_absent (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat) (k : Nat),
    k ∉ lruModel cap ops →
    impl.cachetools.contains
      (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops) k = false

-- ══ Interleaved get+put op-sequence obligations ═══════════════
-- The specs below replay an *interleaved* `get`/`put` trace `ops : List Op`
-- through `impl.cachetools.get` and `impl.cachetools.put` via `applyMixed`.
-- `spec_applyMixed_contents` gives the closed-form recency contents under a
-- mixed trace; the rest are its invariants and corollaries.

/-- Global invariant (mixed): replaying any interleaved `get`/`put` trace
    never changes the cache's `capacity` field — the declared size is a
    fixed attribute of the cache, untouched by reads or writes. -/
def spec_applyMixed_capacity (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (ops : List Op),
    (applyMixed impl.cachetools.get impl.cachetools.put c ops).capacity = c.capacity

/-- Global invariant (mixed): the capacity bound is preserved over an
    arbitrary interleaved trace. From a `Nodup` cache within capacity,
    replaying any `get`/`put` sequence stays within capacity — the cache never
    exceeds its declared size, no matter how reads and writes are interleaved.

    The `Nodup` hypothesis records the standing distinctness invariant (a
    cache never holds the same key twice). -/
def spec_applyMixed_size_le_cap (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (ops : List Op),
    c.order.Nodup →
    c.order.length ≤ c.capacity →
    (applyMixed impl.cachetools.get impl.cachetools.put c ops).order.length ≤ c.capacity

/-- Global invariant (mixed): distinctness of keys is preserved over an
    arbitrary interleaved trace. From a cache whose keys are distinct,
    replaying any `get`/`put` sequence yields a cache whose keys are still
    distinct — neither reads nor writes, in any interleaving, ever cause the
    cache to hold the same key twice. -/
def spec_applyMixed_nodup (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (ops : List Op),
    c.order.Nodup →
    (applyMixed impl.cachetools.get impl.cachetools.put c ops).order.Nodup

/-- Whole-trace characterization (mixed): replaying an interleaved `get`/`put`
    trace `ops` from a fresh capacity-`cap` cache yields exactly the
    closed-form recency contents `keyModel cap ops`. The full functional
    specification of the policy over a mixed operation sequence — which keys
    survive and in what recency order, accounting for both reads (which
    refresh recency of a present key) and writes (which insert and may
    evict). -/
def spec_applyMixed_contents (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Op),
    (applyMixed impl.cachetools.get impl.cachetools.put (impl.cachetools.empty cap) ops).order
      = keyModel cap ops

/-- Membership over mixed sequences: after replaying an interleaved trace
    from empty, a key is present exactly when it survives in the closed-form
    model `keyModel cap ops`. The whole-trace membership law for mixed ops —
    it simultaneously says recently-touched keys survive and stale keys are
    gone. -/
def spec_applyMixed_present_iff (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Op) (k : Nat),
    impl.cachetools.contains
        (applyMixed impl.cachetools.get impl.cachetools.put (impl.cachetools.empty cap) ops) k = true
      ↔ k ∈ keyModel cap ops

/-- Op-sequence final state (mixed): after any trace whose *last* operation
    is a `put k`, into a positive-capacity cache, the most-recently-used key
    (head of `order`) is `k`. Recency is determined by the whole interleaved
    trace, and the freshly-put key always lands at the front regardless of
    the prior `get`/`put` history. -/
def spec_applyMixed_last_put_mru (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Op) (k : Nat),
    0 < cap →
    (applyMixed impl.cachetools.get impl.cachetools.put (impl.cachetools.empty cap)
      (ops ++ [Op.store k])).order.head? = some k

/-- A get-only *suffix* preserves the key SET (only the order changes): for
    any interleaved prefix `base` followed by a suffix `gets` consisting
    solely of `get` operations, a key is present after `base ++ gets` exactly
    when it was present after `base`. Gets reorder the recency but never add
    or drop a key — a read-only run leaves the key set exactly as it found it. -/
def spec_get_only_suffix_preserves_keys (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (base gets : List Op) (k : Nat),
    gets.all Op.isGet = true →
    (impl.cachetools.contains
        (applyMixed impl.cachetools.get impl.cachetools.put (impl.cachetools.empty cap)
          (base ++ gets)) k = true
      ↔ impl.cachetools.contains
        (applyMixed impl.cachetools.get impl.cachetools.put (impl.cachetools.empty cap)
          base) k = true)

-- ══ Stack-distance / reuse and eviction-count laws (put-only) ══
-- The reuse guarantee, the exact net eviction count, and the nodup-prefix
-- shape of the final recency order.

/-- Stack-distance / reuse guarantee: a key `k` that was put (`k ∈ ops`) and
    then had *fewer than `cap`* distinct other keys touched more recently than
    its most recent put is still present after the whole trace — re-reference
    a key before `cap` other distinct keys intervene and it survives.

    The count of distinct keys touched more recently than `k`'s last put is
    `(dedupKeepFirst (takeBefore k ops.reverse)).length`. -/
def spec_reuse_no_evict (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat) (k : Nat),
    k ∈ ops →
    (dedupKeepFirst (takeBefore k ops.reverse)).length < cap →
    impl.cachetools.contains
      (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops) k = true

/-- Total (net) evictions over a put-trace: the number of distinct keys that
    end up evicted — distinct keys ever put but absent from the final cache —
    is exactly `max 0 (d - cap)`, where `d` is the number of distinct keys in
    the trace. A cache of capacity `cap` retains the `cap` most-recent
    distinct keys, so everything beyond that count is gone. This counts the
    *evicted* distinct keys (contrast `spec_final_size_eq`, which counts the
    survivors), giving the exact loss an LRU cache incurs on a workload of `d`
    distinct keys. -/
def spec_total_evictions (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat),
    ((dedupKeepFirst ops.reverse).filter (fun k =>
        !((applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order.elem k))).length
      = max 0 ((dedupKeepFirst ops.reverse).length - cap)

/-- Structural closure: the recency order after a put-trace is a
    duplicate-free *prefix* of the full distinct-key recency list of the
    trace — bounding the cache to its capacity only ever discards a
    least-recent suffix, never reordering or duplicating what remains. This
    pins the exact shape of the final state: `order` is `Nodup`, and it is an
    initial segment (`<+:`) of `dedupKeepFirst ops.reverse`, the recency
    order an unbounded cache would hold. -/
def spec_lruModel_nodup_prefix (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat),
    let ord := (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order
    ord.Nodup ∧ ord <+: dedupKeepFirst ops.reverse

-- ══ Whole-trace laws: capacity-monotonicity, eviction-order, stack-distance ══
-- The obligations below compare two runs of the policy (at adjacent
-- capacities), characterize the eviction *events* themselves (which key was
-- dropped, and when, in what order), and pin the LRU survival criterion as a
-- single biconditional over the whole trace.

-- ── Frozen eviction-trace recomputation (DO NOT MODIFY) ───────
-- A paired fold that, alongside the running recency order, records the
-- *sequence of evicted keys in eviction order*. `evStep` mirrors one
-- `store` (a `put`) and records the LRU key it evicts. `evictionTrace` is
-- the frozen reference the spec compares against; it mentions only frozen
-- list operations (never `impl`). The names `evStep`/`evicted`/`evRun`
-- avoid the scored API lexemes.

/-- One step of the eviction-recording model: extend the recency order by
    `k` (moving it to the front), and if that overflows `cap`, drop the
    least-recently-used (last) key and append it to the eviction log. The
    second component accumulates the evicted keys *in eviction order*. -/
def evStep (cap : Nat) : (List Nat × List Nat) → Nat → (List Nat × List Nat)
  | (cur, evicted), k =>
      let moved := k :: cur.filter (fun j => !(j == k))
      if moved.length > cap then (moved.dropLast, evicted ++ [moved.getLast?.getD 0])
      else (moved, evicted)

/-- The closed-form eviction trace of a capacity-`cap` cache replaying the
    put-trace `ops` from empty: the ordered sequence of keys evicted, oldest
    eviction first. This is an independent recomputation of the eviction
    *events* (not just the final contents). -/
def evictionTrace (cap : Nat) (ops : List Nat) : List Nat :=
  (ops.foldl (evStep cap) ([], [])).2

/-- A spec-side paired fold that, using only the supplied `step` (= `put`)
    and frozen list observers on the `.order` field, records — at each
    step — the keys that were present *before* the step but absent *after*
    it (i.e. the keys this `put` evicted), accumulated in eviction order.
    `step` is always instantiated at `impl.cachetools.put`; the helper never
    mentions `impl`. -/
def evRun (step : Lru → Nat → Lru) : (Lru × List Nat) → Nat → (Lru × List Nat)
  | (c, evicted), k =>
      let c' := step c k
      (c', evicted ++ c.order.filter (fun j => !(c'.order.elem j)))

-- ── The hard obligations ──────────────────────────────────────

/-- Capacity monotonicity / anti-eviction: enlarging the capacity only ever
    *adds* keys to the final cache — every key present after replaying a
    put-trace at capacity `cap` is also present after replaying the *same*
    trace at capacity `cap + 1`. The final key set is monotone in capacity:
    giving an LRU cache more room can only help retention, never cause a key
    that the smaller cache kept to be lost.

    This compares the final contents of two runs of the policy over a shared
    trace at adjacent capacities. -/
def spec_cap_monotone_contents (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat) (k : Nat),
    impl.cachetools.contains
        (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops) k = true →
    impl.cachetools.contains
        (applyOps impl.cachetools.put (impl.cachetools.empty (cap + 1)) ops) k = true

/-- Eviction order is a function of the whole trace: the sequence of keys
    evicted while replaying a put-trace from empty — each step's evicted key
    recorded in eviction order via `evRun` — equals the independent
    recomputation `evictionTrace cap ops`, for positive capacity. This
    characterizes the eviction *events* themselves (which key was dropped, and
    when, in what order), not merely the final contents. -/
def spec_eviction_trace (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat),
    0 < cap →
    (ops.foldl (evRun impl.cachetools.put) (impl.cachetools.empty cap, [])).2
      = evictionTrace cap ops

/-- Stack-distance characterization (bidirectional): after replaying a
    put-trace from empty, a key `k` is present *if and only if* it was ever
    put (`k ∈ ops`) AND fewer than `cap` distinct *other* keys were touched
    more recently than `k`'s most recent put — i.e. its reuse distance
    `(dedupKeepFirst (takeBefore k ops.reverse)).length` is below `cap`. The
    exact LRU survival criterion as a single `↔` over the whole trace: close-
    reuse keys survive, far-reuse keys are gone. -/
def spec_present_iff_reuse_distance (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat) (k : Nat),
    (impl.cachetools.contains
        (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops) k = true)
      ↔ (k ∈ ops ∧ (dedupKeepFirst (takeBefore k ops.reverse)).length < cap)

/-- Confluence under idempotent collapse: collapsing two adjacent identical
    puts anywhere in a put-trace leaves the final cache unchanged (whole-cache
    equality — capacity *and* recency order), for any surrounding prefix `xs`
    and suffix `ys`. -/
def spec_collapse_adjacent_dup (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (xs ys : List Nat) (k : Nat),
    applyOps impl.cachetools.put (impl.cachetools.empty cap) (xs ++ k :: k :: ys)
      = applyOps impl.cachetools.put (impl.cachetools.empty cap) (xs ++ k :: ys)

-- ══ Two-run comparison and trace-extension laws ══════════════════════════
-- Each obligation below states a clean end-fact: capacity-monotone recency
-- prefixes, prefix-monotonicity of the eviction history under trace
-- extension, capacity-monotonicity of the eviction-event count, and
-- persistence of an evicted key under continuations that never re-insert it.

/-- Capacity-monotone recency PREFIX (two-run comparison): the recency order
    after replaying a put-trace at capacity `cap` is a *prefix* (`<+:`) of the
    order after the same trace at capacity `cap + 1`. Raising the capacity by
    one only ever extends the recency tail with one more (less-recent) key. -/
def spec_cap_monotone_order_prefix (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat),
    (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order
      <+: (applyOps impl.cachetools.put (impl.cachetools.empty (cap + 1)) ops).order

/-- Eviction-history is PREFIX-MONOTONE under trace extension: the sequence of
    keys evicted while replaying a prefix `xs` (recorded by `evRun`, in
    eviction order) is a *prefix* (`<+:`) of the sequence evicted while
    replaying the longer trace `xs ++ ys`. The eviction log is append-only. -/
def spec_eviction_trace_prefix_monotone (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (xs ys : List Nat),
    (xs.foldl (evRun impl.cachetools.put) (impl.cachetools.empty cap, [])).2
      <+: ((xs ++ ys).foldl (evRun impl.cachetools.put) (impl.cachetools.empty cap, [])).2

/-- Eviction-event COUNT is monotone in capacity: the number of eviction
    events while replaying a put-trace at capacity `cap + 1` is at most the
    number at capacity `cap` (positive `cap`). More room never causes more
    evictions.

    This counts eviction *events*, not net distinct evictions: a key can be
    evicted, re-put, and evicted again, so this is NOT the closed-form
    `max 0 (#distinct − cap)` of `spec_total_evictions`. The `0 < cap`
    hypothesis is required — the inequality genuinely fails at `cap = 0`. -/
def spec_eviction_count_cap_monotone (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat),
    0 < cap →
    ((ops.foldl (evRun impl.cachetools.put) (impl.cachetools.empty (cap + 1), [])).2).length
      ≤ ((ops.foldl (evRun impl.cachetools.put) (impl.cachetools.empty cap, [])).2).length

/-- Eviction PERSISTENCE: once a key `k` is absent from the cache after a
    trace `ops`, replaying any continuation `more` that never re-inserts `k`
    (every key in `more` is `≠ k`) leaves `k` absent. A dropped key stays
    dropped until it is explicitly re-`put` — the cache never spontaneously
    resurrects an evicted key from operations on other keys.

    The statement relates the two endpoint absences (after `ops`, and after
    `ops ++ more`) under the side condition that `more` never touches `k`. -/
def spec_evicted_persists (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops more : List Nat) (k : Nat),
    impl.cachetools.contains
        (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops) k = false →
    more.all (fun j => !(j == k)) = true →
    impl.cachetools.contains
        (applyOps impl.cachetools.put (impl.cachetools.empty cap) (ops ++ more)) k = false

-- ══ Forgetting / saturation, exact size, and op-equivalence laws ══
-- A further family of end-facts: prefix-forgetting under a saturating suffix,
-- the exact final size, a get-only-from-empty no-op, eviction provenance, and
-- two `get`/`put` equivalences on a present or just-put key.

/-- Prefix-forgetting under a saturating suffix: if a suffix `ys` introduces at
    least `cap` distinct keys (`cap ≤ (dedupKeepFirst ys.reverse).length`), then
    replaying `xs ++ ys` from empty yields the *same* cache (capacity *and*
    recency order) as replaying `ys` alone — a saturating suffix completely
    overwrites the working set, so the prefix `xs` becomes unobservable. -/
def spec_suffix_saturates (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (xs ys : List Nat),
    cap ≤ (dedupKeepFirst ys.reverse).length →
    applyOps impl.cachetools.put (impl.cachetools.empty cap) (xs ++ ys)
      = applyOps impl.cachetools.put (impl.cachetools.empty cap) ys

/-- Exact final size: after replaying a put-trace from empty, the cache holds
    exactly `min cap d` keys, where `d` is the number of distinct keys in the
    trace (`(dedupKeepFirst ops.reverse).length`). The size saturates at the
    capacity once enough distinct keys have been seen, and otherwise equals the
    distinct-key count. Distinct from `spec_total_evictions` (which counts the
    *evicted* keys); this counts the *survivors*. -/
def spec_final_size_eq (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat),
    (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order.length
      = min cap (dedupKeepFirst ops.reverse).length

/-- A get-only trace from a fresh cache is the identity (whole STATE):
    replaying an interleaved trace `gets` consisting solely of `get`
    operations from `empty cap` leaves the cache exactly `empty cap`. -/
def spec_get_only_from_empty_noop (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (gets : List Op),
    gets.all Op.isGet = true →
    applyMixed impl.cachetools.get impl.cachetools.put (impl.cachetools.empty cap) gets
      = impl.cachetools.empty cap

/-- Eviction provenance: every key ever recorded as evicted while replaying a
    put-trace from empty (via the paired fold `evRun`) was itself put — it occurs
    in `ops`. The cache never fabricates an eviction victim out of thin air; a key
    can only be dropped if it was inserted at some earlier point in the trace. -/
def spec_evicted_were_put (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat) (k : Nat),
    0 < cap →
    k ∈ (ops.foldl (evRun impl.cachetools.put) (impl.cachetools.empty cap, [])).2 →
    k ∈ ops

/-- Re-getting a just-put key is a whole-state no-op: `get (put c k) k = put c k`.
    Holds at *every* capacity, including the degenerate `cap = 0`. -/
def spec_get_after_put_noop (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    impl.cachetools.get (impl.cachetools.put c k) k = impl.cachetools.put c k

/-- `put` and `get` agree on a present key within capacity: if `k` is present
    in a `Nodup` cache within capacity, then `put c k = get c k` (whole state).
    The `Nodup` and within-capacity hypotheses record the standing cache
    invariants. -/
def spec_put_eq_get_present (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    impl.cachetools.contains c k = true →
    c.order.Nodup →
    c.order.length ≤ c.capacity →
    impl.cachetools.put c k = impl.cachetools.get c k

-- ══ Positional / frame / recency-anchor laws ══
-- A final family of end-facts: the positional slot of a survivor (its
-- recency rank), the whole-STATE transparency of a read-only run over unseen
-- keys, and the recency-anchor tie between the head of the order and the last
-- effective write.

-- ── Frozen touched-key extractor (DO NOT MODIFY) ──────────────
-- `touchedKeys` collects the key argument of every op in a mixed trace,
-- referencing only the frozen `Op` alphabet and list operations (never
-- `impl`), so it is safe to share across obligations that quantify over the
-- keys a trace mentions.

/-- The list of keys mentioned by a mixed trace, in order (both `touch` and
    `store` carry a key). Used to state that a read-only suffix touches only
    keys the cache does not currently hold. -/
def touchedKeys : List Op → List Nat
  | [] => []
  | Op.touch k :: rest => k :: touchedKeys rest
  | Op.store k :: rest => k :: touchedKeys rest

/-- Whole-STATE transparency of an unproductive read-only run: if a suffix
    `gets` consists solely of `get` operations AND every key it touches is
    *absent* from the cache reached after the prefix `base`, then replaying
    `base ++ gets` yields the *exact same cache* (capacity AND recency order)
    as replaying `base` alone.

    The absence side-condition is stated positively over `touchedKeys gets`:
    every touched key `k` has `contains … k = false` after `base`. -/
def spec_get_absent_suffix_noop (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (base gets : List Op),
    gets.all Op.isGet = true →
    (touchedKeys gets).all (fun k =>
        !(impl.cachetools.contains
            (applyMixed impl.cachetools.get impl.cachetools.put
              (impl.cachetools.empty cap) base) k)) = true →
    applyMixed impl.cachetools.get impl.cachetools.put (impl.cachetools.empty cap)
        (base ++ gets)
      = applyMixed impl.cachetools.get impl.cachetools.put (impl.cachetools.empty cap) base

/-- Recency-RANK / positional slot of a survivor: after replaying a put-trace
    from empty, a key `k` whose reuse distance `d` (the number of distinct
    *other* keys touched more recently than `k`'s most recent put,
    `d = (dedupKeepFirst (takeBefore k ops.reverse)).length`) is below capacity
    sits at *exactly* position `d` of the recency order — dropping the `d`
    more-recent keys leaves `k` at the front (`(order.drop d).head? = some k`).
    This pins the survivor's *position*, not merely its presence.

    The `d < cap` hypothesis is the survival criterion of
    `spec_present_iff_reuse_distance`; under it `k` is guaranteed present. -/
def spec_survivor_index (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat) (k : Nat),
    k ∈ ops →
    (dedupKeepFirst (takeBefore k ops.reverse)).length < cap →
    ((applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order.drop
        (dedupKeepFirst (takeBefore k ops.reverse)).length).head? = some k

/-- Recency-anchor tie between the MRU head and zero reuse distance: after
    replaying a put-trace from empty into a positive-capacity cache, the head of
    the recency order is `some k` *if and only if* `k` was put and no distinct
    key was touched more recently than `k`'s most recent put (its reuse distance
    is `0`). The MRU slot is characterized combinatorially: it is exactly the
    unique most-recently-put distinct key.

    This bridges the head observer (`order.head?`) and the stack-distance
    measure (`takeBefore`/`dedupKeepFirst`). -/
def spec_mru_iff_reuse_distance_zero (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat) (k : Nat),
    0 < cap →
    ((applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order.head? = some k
      ↔ (k ∈ ops ∧ (dedupKeepFirst (takeBefore k ops.reverse)).length = 0))

-- ══ Multiplicity / renaming / tail-anchor / drop-suffix eviction laws ══
-- A further family of clean end-facts pinning finer structure of the
-- policy: a per-key multiplicity accounting split, a tail (eviction-victim)
-- recency-rank characterization, uniqueness of the final recency order among
-- recency-ordered candidates, invariance of the whole final state under an
-- injective key renaming, and a suffix-anchored recomputation of the
-- eviction-event sequence.

/-- Per-key multiplicity accounting over the whole distinct-key history: for
    every key `k`, its multiplicity in the final recency order plus its
    multiplicity among the distinct keys of the trace that are absent from the
    final cache equals its multiplicity in the full distinct-key recency list
    `dedupKeepFirst ops.reverse`. Every distinct key the trace ever put is
    accounted for exactly once — either it survives or it was evicted, never
    both and never neither. -/
def spec_distinct_key_count_partition (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat) (k : Nat),
    ((applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order.count k)
      + (((dedupKeepFirst ops.reverse).filter (fun j =>
          !((applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order.elem j))).count k)
      = (dedupKeepFirst ops.reverse).count k

/-- Eviction-victim recency-rank characterization: after replaying a put-trace
    from empty, the reported LRU key (`lruKey`) is `some k` exactly when `k` was
    put into a positive-capacity cache AND `k`'s reuse rank — one more than the
    number of distinct keys touched more recently than `k`'s most recent put —
    equals the cache's final occupancy `min cap (#distinct)`. The eviction
    victim is pinned combinatorially: it is precisely the least-recent surviving
    key, at the final retained recency slot. -/
def spec_lruKey_reuse_distance_tail (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat) (k : Nat),
    impl.cachetools.lruKey
        (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops) = some k
      ↔ (k ∈ ops ∧ 0 < cap ∧
          (dedupKeepFirst (takeBefore k ops.reverse)).length + 1 =
            min cap (dedupKeepFirst ops.reverse).length)

/-- Uniqueness of the final recency order among recency-ordered candidates: any
    duplicate-free list `xs` that is an initial segment (`<+:`) of the full
    distinct-key recency list `dedupKeepFirst ops.reverse` and has exactly the
    same membership as the final cache order must BE the final cache order. The
    final state is the unique recency-ordered key set of its size — membership
    plus the recency ordering determines the order completely. -/
def spec_final_order_unique_recency_prefix (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops xs : List Nat),
    xs.Nodup →
    xs <+: dedupKeepFirst ops.reverse →
    (∀ k : Nat,
      k ∈ xs ↔
        k ∈ (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order) →
    xs = (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order

/-- Injective key-renaming frame: relabelling every key of a put-trace by an
    injective function `f` relabels the whole final cache the same way — the
    capacity is unchanged and the final recency order is exactly the `f`-image
    of the un-renamed final order. The eviction policy depends only on key
    equality, so it commutes with any injective renaming of the key space. -/
def spec_applyOps_injective_rename_state (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat) (f : Nat → Nat),
    Function.Injective f →
    applyOps impl.cachetools.put (impl.cachetools.empty cap) (ops.map f)
      = { capacity :=
            (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).capacity,
          order :=
            (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order.map f }

-- ══ Over-capacity direct-input truncation, split-frame, and victim-recency laws ══
-- A family of clean end-facts anchored on `put`/`get`/`lruKey` applied to
-- DIRECT over-capacity `Lru` inputs (order.length beyond capacity, the standing
-- `Nodup` invariant carried explicitly), on the whole-order split around a key,
-- and on the recency-victim (`getLast?`/`lruKey`) tie to the distinct-key model.
-- Anchored on `List.dropLast`, `List.getLast?`, `List.filter`, `List.count`,
-- `takeBefore`, `dedupKeepFirst`, and `lruModel`.

/-- `put` on an over-capacity direct input truncates exactly one key from the
    least-recently-used tail: for a `Nodup` cache whose `order` already exceeds
    `capacity`, `(put c k).order` is `(k :: c.order.filter (· ≠ k)).dropLast` —
    the moved recency list with its single last (LRU) element removed. Truncation
    always drops from the recency tail, never keeps a `capacity`-length head. -/
def spec_put_overcap_dropLast_exact (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    c.order.Nodup →
    c.capacity < c.order.length →
    (impl.cachetools.put c k).order =
      (k :: c.order.filter (fun j => !(j == k))).dropLast

/-- Inserting an absent key into an over-capacity direct cache drops only the
    old LRU victim: for a `Nodup` cache whose `order` exceeds `capacity`, with
    `k` absent and `c.order.getLast? = some victim`, a key `j` is present after
    the `put` exactly when it is `k` or an old key other than `victim`. Exactly
    the least-recent key leaves; every other key survives. -/
def spec_put_overcap_absent_survivors (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k victim j : Nat),
    c.order.Nodup →
    k ∉ c.order →
    c.capacity < c.order.length →
    c.order.getLast? = some victim →
    (j ∈ (impl.cachetools.put c k).order ↔
      j = k ∨ (j ∈ c.order ∧ j ≠ victim))

/-- Membership form of single-victim eviction at or beyond capacity: for a
    `Nodup` cache with `0 < capacity ≤ order.length`, inserting an absent `k`
    leaves present exactly `k` together with every old key other than the LRU
    victim `c.order.getLast?`. Stated over `contains` for every key `j`. -/
def spec_put_absent_overflow_only_drops_old_lru (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k victim j : Nat),
    0 < c.capacity →
    c.capacity ≤ c.order.length →
    c.order.Nodup →
    impl.cachetools.contains c k = false →
    c.order.getLast? = some victim →
    (impl.cachetools.contains (impl.cachetools.put c k) j = true ↔
      j = k ∨ (j ∈ c.order ∧ j ≠ victim))

/-- Whole-state split frame around a present key: for a `Nodup` cache whose
    `order` splits as `newer ++ (k :: older)`, `get c k` moves `k` to the MRU
    head leaving every other key in its original relative order
    (`k :: (newer ++ older)`), and `put c k` yields that same moved order,
    truncated by one LRU key exactly when it overflows `capacity`. Pins the
    entire resulting state, not merely membership. -/
def spec_existing_key_split_frame (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat) (newer older : List Nat),
    c.order.Nodup →
    c.order = newer ++ (k :: older) →
    (impl.cachetools.get c k =
      { capacity := c.capacity, order := k :: (newer ++ older) }) ∧
    (impl.cachetools.put c k =
      { capacity := c.capacity,
        order :=
          if (k :: (newer ++ older)).length > c.capacity then
            (k :: (newer ++ older)).dropLast
          else
            k :: (newer ++ older) })

/-- First-occurrence recency frame of a `get` hit on an over-capacity direct
    cache: for a `Nodup` cache whose `order` exceeds `capacity`, touching a
    present `k` sets, for every other key `j`, the recency prefix before `j`
    (`takeBefore j`) to `k` followed by the old prefix with `k` removed. Only
    `k` moves to the front; every other key's first-occurrence position frame
    is preserved. -/
def spec_get_overcap_takeBefore_frame (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k j : Nat),
    c.capacity < c.order.length →
    c.order.Nodup →
    impl.cachetools.contains c k = true →
    j ≠ k →
    takeBefore j (impl.cachetools.get c k).order =
      k :: (takeBefore j c.order).filter (fun x => !(x == k))

/-- Touching a non-LRU key leaves the eviction victim unchanged: for a `Nodup`
    cache with `lruKey c = some victim`, a `get` of a present key `k ≠ victim`
    still reports `victim` as the LRU key. Promoting a non-tail key never
    disturbs the tail. -/
def spec_get_non_lru_preserves_lruKey (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k victim : Nat),
    c.order.Nodup →
    impl.cachetools.contains c k = true →
    impl.cachetools.lruKey c = some victim →
    k ≠ victim →
    impl.cachetools.lruKey (impl.cachetools.get c k) = some victim

/-- Touching the current LRU promotes it, so the old penultimate becomes the
    new victim: for a `Nodup` cache with `lruKey c = some k` and
    `(c.order.dropLast).getLast? = some newVictim`, a `get c k` reports
    `newVictim` as the new LRU key. -/
def spec_get_lru_hit_lruKey_penultimate (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k newVictim : Nat),
    c.order.Nodup →
    impl.cachetools.lruKey c = some k →
    (c.order.dropLast).getLast? = some newVictim →
    impl.cachetools.lruKey (impl.cachetools.get c k) = some newVictim

/-- The reported LRU victim sits exactly at the recency tail: for a `Nodup`
    cache with `lruKey c = some victim`, the recency prefix before `victim`
    (`takeBefore victim`) is `c.order.dropLast` — `victim`'s first (hence only)
    occurrence is the final position of `order`. -/
def spec_lruKey_takeBefore_dropLast (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (victim : Nat),
    c.order.Nodup →
    impl.cachetools.lruKey c = some victim →
    takeBefore victim c.order = c.order.dropLast

/-- Per-key multiplicity after a put-trace equals that of the retained distinct
    recency prefix: for every key `k`, its `count` in the final recency order
    after replaying `ops` from empty equals its `count` in
    `(dedupKeepFirst ops.reverse).take cap`. Ties the final contents keywise to
    the closed-form model. -/
def spec_applyOps_count_dedup_prefix (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat) (k : Nat),
    (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops).order.count k =
      ((dedupKeepFirst ops.reverse).take cap).count k

/-- After a put-trace from empty the reported LRU victim is the last key of the
    retained distinct recency prefix: `lruKey` of the replayed cache equals
    `((dedupKeepFirst ops.reverse).take cap).getLast?`. The eviction victim over
    a whole trace is the least-recent survivor of the distinct-key model. -/
def spec_applyOps_lruKey_model_getLast (impl : RepoImpl) : Prop :=
  ∀ (cap : Nat) (ops : List Nat),
    impl.cachetools.lruKey (applyOps impl.cachetools.put (impl.cachetools.empty cap) ops)
      = ((dedupKeepFirst ops.reverse).take cap).getLast?

/-- `put` pins its ENTIRE result order as a deterministic final state on ANY
    input cache, including one whose `order` is already over capacity. Moving `k`
    to the front and deduplicating gives `moved = k :: order.filter (≠ k)`; if
    that overflows capacity the LRU (last) key is evicted by `dropLast`, else
    `moved` is kept verbatim. This is the exact one-step transition law: it holds
    for arbitrary starting states, not only the within-capacity or empty-start
    cases the other `put` laws assume, so it distinguishes the genuine
    move-to-front-then-drop-LRU policy from any impl that evicts differently on
    over-capacity input (e.g. `moved.take capacity`, which forgets the whole tail
    rather than dropping only the single LRU key). -/
def spec_put_order_exact (impl : RepoImpl) : Prop :=
  ∀ (c : Lru) (k : Nat),
    (impl.cachetools.put c k).order =
      (let moved := k :: c.order.filter (fun j => !(j == k))
       if moved.length > c.capacity then moved.dropLast else moved)
