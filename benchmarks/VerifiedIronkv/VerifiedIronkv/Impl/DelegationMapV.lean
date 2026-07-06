import VerifiedIronkv.Impl.DelegationMapT
-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedIronkv.Impl.DelegationMapV

Translated Verus vocabulary and reference implementations for `DelegationMapV`.

DO NOT MODIFY types or signatures. Implement only the marked function bodies.
-/

structure StrictlyOrderedVec (K : Type) where
  v : List K
  deriving Repr, DecidableEq, BEq, Inhabited

abbrev ID := EndPoint

structure StrictlyOrderedMap (K : Type) where
  keys : StrictlyOrderedVec K
  vals : List ID
  m : List (K × ID)
  deriving Repr, DecidableEq, BEq, Inhabited

def orderingLtBool : KeyOrdering → Bool
  | KeyOrdering.Less => true
  | _ => false

def orderingLeBool : KeyOrdering → Bool
  | KeyOrdering.Less => true
  | KeyOrdering.Equal => true
  | KeyOrdering.Greater => false

def keyIteratorLt {K : Type} [KeyTrait K] (lo hi : KeyIterator K) : Bool :=
  match lo.k, hi.k with
  | some loK, some hiK => orderingLtBool (KeyTrait.cmp_spec loK hiK)
  | some _, none => true
  | _, _ => false

def keyIteratorBetween {K : Type} [KeyTrait K] (lo ki hi : KeyIterator K) : Bool :=
  match lo.k, ki.k, hi.k with
  | some loK, some k, some hiK => orderingLeBool (KeyTrait.cmp_spec loK k) && orderingLtBool (KeyTrait.cmp_spec k hiK)
  | some loK, some k, none => orderingLeBool (KeyTrait.cmp_spec loK k)
  | _, _, _ => false

def keyRangeContains {K : Type} [KeyTrait K] (kr : KeyRange K) (k : K) : Bool :=
  keyIteratorBetween kr.lo { k := some k } kr.hi

/-- Lawfulness of a `KeyTrait` comparator: `cmp_spec` is a total order.

Upstream Verus/IronKV's `KeyTrait` carries a `properties()` lemma establishing
that `cmp` is a total order; the Lean `KeyTrait` record dropped those laws. This
class restores them as the semantic assumption the delegation-map range specs
rely on. The key law is `le_lt_trans`: it is exactly what makes an empty
iterator range (`keyIteratorLt lo hi = false`) contain no keys, so the
`keyIteratorLt`-based emptiness short-circuit in `set_l1115` /
`range_consistent_impl` is sound. `cmp_refl` and `cmp_antisymm` complete the
total-order picture and document the intended lawfulness. -/
class LawfulKeyTrait (K : Type) [KeyTrait K] : Prop where
  cmp_refl : ∀ a : K, KeyTrait.cmp_spec a a = KeyOrdering.Equal
  cmp_antisymm : ∀ a b : K,
    orderingLeBool (KeyTrait.cmp_spec a b) = true →
    orderingLeBool (KeyTrait.cmp_spec b a) = true → a = b
  le_lt_trans : ∀ a b c : K,
    orderingLeBool (KeyTrait.cmp_spec a b) = true →
    orderingLtBool (KeyTrait.cmp_spec b c) = true →
    orderingLtBool (KeyTrait.cmp_spec a c) = true
  -- Connexity: a genuine total order cannot have `a > b` and `b > a` at once.
  -- Without this, an "order" with a mutually-`Greater` pair (e.g. `cmp b c =
  -- cmp c b = Greater`) satisfies the other three laws only vacuously (the
  -- `≤`/`<` premises are `false` on `Greater`), so it slips through and makes
  -- the delegation-map range specs unsatisfiable. This law forces `Greater`
  -- to be the mirror of `Less`, ruling out such pseudo-orders.
  cmp_swap : ∀ a b : K,
    KeyTrait.cmp_spec a b = KeyOrdering.Greater ↔
      KeyTrait.cmp_spec b a = KeyOrdering.Less
  -- `zero_spec` is the least key. This mirrors the upstream `KeyTrait` contract
  -- (verus-lang/verified-ironkv `ironsht/src/keys_t.rs`: `zero_spec < k` for
  -- every distinct key). `strictlyOrderedMapValid` requires a breakpoint at
  -- `zero_spec`; without this law an order whose `zero_spec` is not minimal
  -- (e.g. `Bool` with `false < true` and `zero_spec = true`) lets `set_l1115`
  -- erase the mandatory `zero_spec` breakpoint over a range that starts below
  -- it, so the post-state is invalid and `set_updates_range` becomes falsifiable.
  zero_lt : ∀ k : K,
    k ≠ KeyTrait.zero_spec → KeyTrait.cmp_spec KeyTrait.zero_spec k = KeyOrdering.Less

/-- `SHTKey`'s `≤`-comparator agrees with `Nat.≤` on the `ukey` field. -/
theorem shtKeyLeBool_iff (a b : SHTKey) :
    orderingLeBool (KeyTrait.cmp_spec a b) = true ↔ a.ukey ≤ b.ukey := by
  show orderingLeBool (if a.ukey < b.ukey then _ else if a.ukey = b.ukey then _ else _) = true ↔ _
  rcases Nat.lt_trichotomy a.ukey b.ukey with h | h | h
  · rw [if_pos h]; simp [orderingLeBool]; omega
  · rw [if_neg (by omega), if_pos h]; simp [orderingLeBool]; omega
  · rw [if_neg (by omega), if_neg (by omega)]; simp [orderingLeBool]; omega

/-- `SHTKey`'s `<`-comparator agrees with `Nat.<` on the `ukey` field. -/
theorem shtKeyLtBool_iff (a b : SHTKey) :
    orderingLtBool (KeyTrait.cmp_spec a b) = true ↔ a.ukey < b.ukey := by
  show orderingLtBool (if a.ukey < b.ukey then _ else if a.ukey = b.ukey then _ else _) = true ↔ _
  rcases Nat.lt_trichotomy a.ukey b.ukey with h | h | h
  · rw [if_pos h]; simp only [orderingLtBool, true_iff]; exact h
  · rw [if_neg (by omega), if_pos h]; simp only [orderingLtBool]
    constructor
    · intro hc; simp at hc
    · omega
  · rw [if_neg (by omega), if_neg (by omega)]; simp only [orderingLtBool]
    constructor
    · intro hc; simp at hc
    · omega

/-- The concrete key type `SHTKey` (also `CKey` / `AbstractKey`) compares by its
`ukey : Nat` field, which is a lawful total order. This instance is what makes
the delegation-map range specs non-vacuously true of `canonical` (which is only
ever instantiated at `SHTKey`). -/
instance : LawfulKeyTrait SHTKey where
  cmp_refl a := by
    show (if a.ukey < a.ukey then _ else if a.ukey = a.ukey then _ else _) = _
    simp
  cmp_antisymm a b hab hba := by
    rw [shtKeyLeBool_iff] at hab hba
    have : a.ukey = b.ukey := by omega
    cases a; cases b; simp_all
  le_lt_trans a b c hab hbc := by
    rw [shtKeyLeBool_iff] at hab
    rw [shtKeyLtBool_iff] at hbc ⊢
    omega
  cmp_swap a b := by
    show (if a.ukey < b.ukey then _ else if a.ukey = b.ukey then _ else _) = KeyOrdering.Greater ↔
      (if b.ukey < a.ukey then _ else if b.ukey = a.ukey then _ else _) = KeyOrdering.Less
    rcases Nat.lt_trichotomy a.ukey b.ukey with h | h | h
    · rw [if_pos h, if_neg (by omega), if_neg (by omega)]; simp
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_pos (by omega)]; simp
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]; simp
  zero_lt k hk := by
    -- SHTKey.zero_spec = { ukey := 0 }; k ≠ zero ⇒ k.ukey ≠ 0 ⇒ 0 < k.ukey ⇒ cmp = Less
    have hne : k.ukey ≠ 0 := by
      intro hz; apply hk; cases k; subst hz; rfl
    show (if (0 : Nat) < k.ukey then _ else if (0 : Nat) = k.ukey then _ else _) = KeyOrdering.Less
    rw [if_pos (by omega)]

def keyLeBool {K : Type} [KeyTrait K] (a b : K) : Bool :=
  orderingLeBool (KeyTrait.cmp_spec a b)

def keyLtBool {K : Type} [KeyTrait K] (a b : K) : Bool :=
  orderingLtBool (KeyTrait.cmp_spec a b)

def strictlySortedKeys {K : Type} [KeyTrait K] : List K → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => keyLtBool a b && strictlySortedKeys (b :: rest)

structure DelegationRange (K : Type) where
  lo : KeyIterator K
  hi : KeyIterator K
  dst : AbstractEndPoint
  deriving Repr, DecidableEq, BEq, Inhabited

structure DelegationGhostMap (K : Type) where
  default : AbstractEndPoint
  updates : List (DelegationRange K)
  deriving Repr, DecidableEq, BEq, Inhabited

def delegationGhostMapTotal {K : Type} (default : AbstractEndPoint) : DelegationGhostMap K :=
  { default := default, updates := [] }

def delegationGhostMapLookup? {K : Type} [KeyTrait K]
    (updates : List (DelegationRange K)) (k : K) : Option AbstractEndPoint :=
  match updates with
  | [] => none
  | r :: rest =>
      if keyRangeContains { lo := r.lo, hi := r.hi } k then
        some r.dst
      else
        delegationGhostMapLookup? rest k

def delegationGhostMapView {K : Type} [KeyTrait K]
    (m : DelegationGhostMap K) : K → AbstractEndPoint :=
  fun k =>
    match delegationGhostMapLookup? m.updates k with
    | some ep => ep
    | none => m.default

def delegationGhostMapSetRange {K : Type} [KeyTrait K]
    (m : DelegationGhostMap K) (lo hi : KeyIterator K) (dst : ID) : DelegationGhostMap K :=
  { m with updates := { lo := lo, hi := hi, dst := ioTView dst } :: m.updates }

theorem delegationGhostMapTotal_view {K : Type} [KeyTrait K]
    (default : AbstractEndPoint) (k : K) :
    delegationGhostMapView (delegationGhostMapTotal default) k = default := by
  rfl

theorem delegationGhostMapSetRange_view_hit {K : Type} [KeyTrait K]
    (m : DelegationGhostMap K) (lo hi : KeyIterator K) (dst : ID) (k : K)
    (h : keyRangeContains { lo := lo, hi := hi } k = true) :
    delegationGhostMapView (delegationGhostMapSetRange m lo hi dst) k = ioTView dst := by
  simp [delegationGhostMapView, delegationGhostMapSetRange, delegationGhostMapLookup?, h]

theorem delegationGhostMapSetRange_view_miss {K : Type} [KeyTrait K]
    (m : DelegationGhostMap K) (lo hi : KeyIterator K) (dst : ID) (k : K)
    (h : keyRangeContains { lo := lo, hi := hi } k = false) :
    delegationGhostMapView (delegationGhostMapSetRange m lo hi dst) k =
      delegationGhostMapView m k := by
  simp [delegationGhostMapView, delegationGhostMapSetRange, delegationGhostMapLookup?, h]

structure DelegationMap (K : Type) where
  lows : StrictlyOrderedMap K
  m : DelegationGhostMap K
  default : AbstractEndPoint
  overrides : List (K × AbstractEndPoint)
  ranges : List (DelegationRange K)
  deriving Repr, DecidableEq, BEq, Inhabited

def breakpointContainsKey {K : Type} [DecidableEq K] (entries : List (K × ID)) (key : K) : Bool :=
  entries.any (fun kv => decide (kv.1 = key))

def keyIteratorStrictlyBetween {K : Type} [KeyTrait K] (lo ki hi : KeyIterator K) : Bool :=
  match lo.k, ki.k, hi.k with
  | some loK, some k, some hiK =>
      orderingLtBool (KeyTrait.cmp_spec loK k) && orderingLtBool (KeyTrait.cmp_spec k hiK)
  | some loK, some k, none =>
      orderingLtBool (KeyTrait.cmp_spec loK k)
  | _, _, _ => false

def strictlyOrderedMapGapModel {K : Type} [KeyTrait K] [DecidableEq K]
    (m : StrictlyOrderedMap K) (lo hi : KeyIterator K) : Prop :=
  ∀ k : K,
    keyIteratorStrictlyBetween lo { k := some k } hi = true →
      breakpointContainsKey m.m k = false

def strictlyOrderedMapFromEntries {K : Type} (entries : List (K × ID)) : StrictlyOrderedMap K :=
  { keys := { v := entries.map Prod.fst }, vals := entries.map Prod.snd, m := entries }

def strictlyOrderedMapLookupAux {K : Type} [KeyTrait K] (key : K) (current : Option ID) : List (K × ID) → Option ID
  | [] => current
  | (k, v) :: rest =>
      if keyLeBool k key then strictlyOrderedMapLookupAux key (some v) rest else current

def strictlyOrderedMapLookup? {K : Type} [KeyTrait K] (m : StrictlyOrderedMap K) (key : K) : Option ID :=
  strictlyOrderedMapLookupAux key none m.m

def strictlyOrderedMapLookupWithDefault {K : Type} [KeyTrait K] (m : StrictlyOrderedMap K) (default : AbstractEndPoint) (key : K) : ID :=
  match strictlyOrderedMapLookup? m key with
  | some id => id
  | none => { id := default.id }

def delegationMapLookup {K : Type} [KeyTrait K] [DecidableEq K] (self : DelegationMap K) (key : K) : AbstractEndPoint :=
  ioTView (strictlyOrderedMapLookupWithDefault self.lows self.default key)

def view_L1038 {K : Type} [KeyTrait K] [DecidableEq K] (x : DelegationMap K) : K → AbstractEndPoint :=
  fun k => delegationMapLookup x k

def delegationMapSourceGhostViewOf {K : Type} [KeyTrait K]
    (self : DelegationMap K) : K → AbstractEndPoint :=
  delegationGhostMapView self.m

def abstractDelegationMapViewOf (self : DelegationMap AbstractKey) : AbstractKey → AbstractEndPoint :=
  delegationMapSourceGhostViewOf self

def abstractDelegationMapDelegateForKeyRangeIsHostModel (self : DelegationMap AbstractKey) (kr : KeyRange AbstractKey) (id : AbstractEndPoint) : Prop :=
  ∀ k : AbstractKey, keyRangeContains kr k = true → abstractDelegationMapViewOf self k = id

def abstractEndpointPhysicalAddress (ep : AbstractEndPoint) : Bool :=
  decide (ep.id.length < 1048576)

def strictlyOrderedMapValid {K : Type} [KeyTrait K] [DecidableEq K] (m : StrictlyOrderedMap K) : Bool :=
  strictlySortedKeys (m.m.map Prod.fst) &&
  decide (List.Nodup (m.m.map Prod.fst)) &&
  decide (m.keys.v = m.m.map Prod.fst) &&
  decide (m.vals = m.m.map Prod.snd) &&
  breakpointContainsKey m.m (KeyTrait.zero_spec : K) &&
  m.m.all (fun kv => abstractEndpointPhysicalAddress (ioTView kv.2))

def delegationMapValid {K : Type} [KeyTrait K] [DecidableEq K] (x : DelegationMap K) : Bool :=
  strictlyOrderedMapValid x.lows &&
  abstractEndpointPhysicalAddress x.default

def valid_L1041 (x : DelegationMap CKey) : Bool :=
  delegationMapValid x

def delegationMapNewTotalDefault {K : Type} [KeyTrait K] [DecidableEq K] (self : DelegationMap K) (id : ID) : Prop :=
  delegationMapValid self = true ∧
  self.m = delegationGhostMapTotal (ioTView id) ∧
  ∀ k : K, view_L1038 self k = ioTView id ∧ delegationMapSourceGhostViewOf self k = ioTView id

def delegationMapRangeConsistent {K : Type} [KeyTrait K] [DecidableEq K] (self : DelegationMap K) (lo hi : KeyIterator K) (dst : ID) : Prop :=
  ∀ k : K, keyRangeContains { lo := lo, hi := hi } k = true → view_L1038 self k = ioTView dst

def delegationMapSetUpdatesRange {K : Type} [KeyTrait K] [DecidableEq K] (pre post : DelegationMap K) (lo hi : KeyIterator K) (dst : ID) : Prop :=
  delegationMapRangeConsistent post lo hi dst ∧
  ∀ k : K, keyRangeContains { lo := lo, hi := hi } k = false → view_L1038 post k = view_L1038 pre k

def delegationMapConcreteGhostAgreement {K : Type} [KeyTrait K] [DecidableEq K]
    (self : DelegationMap K) : Prop :=
  ∀ k : K, view_L1038 self k = delegationMapSourceGhostViewOf self k

def delegationMapGhostTotalViewBridge {K : Type} [KeyTrait K] [DecidableEq K]
    (self : DelegationMap K) (ghostView : K → AbstractEndPoint) : Prop :=
  ∀ k : K, ghostView k = delegationMapSourceGhostViewOf self k

def delegationMapSourceValidGapBridge {K : Type} [KeyTrait K] [DecidableEq K]
    (self : DelegationMap K) (ghostView : K → AbstractEndPoint) : Prop :=
  (∀ k : K, abstractEndpointPhysicalAddress (ghostView k) = true) ∧
  ∀ (i k : K) (j : KeyIterator K),
    breakpointContainsKey self.lows.m i = true →
    strictlyOrderedMapGapModel self.lows { k := some i } j →
    keyIteratorBetween { k := some i } { k := some k } j = true →
      ghostView k = ioTView (strictlyOrderedMapLookupWithDefault self.lows self.default i)

def delegationMapBreakpointCoverageBridge {K : Type} [KeyTrait K] [DecidableEq K]
    (self : DelegationMap K) : Prop :=
  ∀ k : K, ∃ i : K, ∃ j : KeyIterator K,
    breakpointContainsKey self.lows.m i = true ∧
    strictlyOrderedMapGapModel self.lows { k := some i } j ∧
    keyIteratorBetween { k := some i } { k := some k } j = true ∧
    view_L1038 self k =
      ioTView (strictlyOrderedMapLookupWithDefault self.lows self.default i)

def delegationMapGhostRangeConsistent {K : Type} [KeyTrait K]
    (ghostView : K → AbstractEndPoint) (lo hi : KeyIterator K) (dst : ID) : Prop :=
  ∀ k : K, keyRangeContains { lo := lo, hi := hi } k = true → ghostView k = ioTView dst

def delegationMapSourceGhostView {K : Type} [KeyTrait K] [DecidableEq K]
    (self : DelegationMap K) (ghostView : K → AbstractEndPoint) : Prop :=
  delegationMapValid self = true ∧
  self.m.default = self.default ∧
  delegationMapGhostTotalViewBridge self ghostView ∧
  delegationMapConcreteGhostAgreement self ∧
  delegationMapSourceValidGapBridge self ghostView ∧
  delegationMapBreakpointCoverageBridge self

def delegationMapSourceValid {K : Type} [KeyTrait K] [DecidableEq K]
    (self : DelegationMap K) : Prop :=
  delegationMapSourceGhostView self (delegationMapSourceGhostViewOf self)

theorem delegationMapSourceValid_view_eq_source {K : Type} [KeyTrait K] [DecidableEq K]
    {self : DelegationMap K} (h : delegationMapSourceValid self) (k : K) :
    view_L1038 self k = delegationMapSourceGhostViewOf self k := by
  rcases h with ⟨_, _, _, hagree, _, _⟩
  exact hagree k

theorem delegationMapSourceValid_get_lookup_eq_source {K : Type} [KeyTrait K] [DecidableEq K]
    {self : DelegationMap K} (h : delegationMapSourceValid self) (k : K) :
    ioTView (strictlyOrderedMapLookupWithDefault self.lows self.default k) =
      delegationMapSourceGhostViewOf self k := by
  exact delegationMapSourceValid_view_eq_source h k

theorem delegationMapSourceValid_range_consistent_iff_source {K : Type}
    [KeyTrait K] [DecidableEq K] {self : DelegationMap K}
    (h : delegationMapSourceValid self) (lo hi : KeyIterator K) (dst : ID) :
    delegationMapRangeConsistent self lo hi dst ↔
      delegationMapGhostRangeConsistent (delegationMapSourceGhostViewOf self) lo hi dst := by
  constructor
  · intro hr k hk
    rw [← delegationMapSourceValid_view_eq_source h k]
    exact hr k hk
  · intro hg k hk
    rw [delegationMapSourceValid_view_eq_source h k]
    exact hg k hk

theorem delegationMapSourceGhostView_unique {K : Type} [KeyTrait K] [DecidableEq K]
    {self : DelegationMap K} {ghostView : K → AbstractEndPoint}
    (h : delegationMapSourceGhostView self ghostView) (k : K) :
    ghostView k = delegationMapSourceGhostViewOf self k := by
  rcases h with ⟨_, _, htotal, _, _, _⟩
  exact htotal k

def delegationMapGhostSetUpdateBridge {K : Type} [KeyTrait K] [DecidableEq K]
    (pre post : DelegationMap K) (preGhost postGhost : K → AbstractEndPoint)
    (lo hi : KeyIterator K) (dst : ID) : Prop :=
  delegationMapGhostTotalViewBridge pre preGhost ∧
  delegationMapGhostTotalViewBridge post postGhost ∧
  delegationMapGhostRangeConsistent postGhost lo hi dst ∧
  ∀ k : K, keyRangeContains { lo := lo, hi := hi } k = false → postGhost k = preGhost k

def delegationMapSourceGhostSetUpdate {K : Type} [KeyTrait K] [DecidableEq K]
    (pre post : DelegationMap K) (preGhost postGhost : K → AbstractEndPoint)
    (lo hi : KeyIterator K) (dst : ID) : Prop :=
  delegationMapSourceGhostView pre preGhost ∧
  delegationMapSourceGhostView post postGhost ∧
  delegationMapGhostRangeConsistent postGhost lo hi dst ∧
  ∀ k : K, keyRangeContains { lo := lo, hi := hi } k = false → postGhost k = preGhost k

def delegationMapGhostHistoryView {K : Type} [KeyTrait K]
    (self : DelegationMap K) : K → AbstractEndPoint :=
  delegationMapSourceGhostViewOf self

def delegationMapGhostHistorySetUpdateBridge {K : Type} [KeyTrait K]
    (pre post : DelegationMap K) (lo hi : KeyIterator K) (dst : ID) : Prop :=
  post.ranges = { lo := lo, hi := hi, dst := ioTView dst } :: pre.ranges ∧
  post.m = delegationGhostMapSetRange pre.m lo hi dst ∧
  delegationMapGhostRangeConsistent (delegationMapGhostHistoryView post) lo hi dst ∧
  ∀ k : K,
    keyRangeContains { lo := lo, hi := hi } k = false →
      delegationMapGhostHistoryView post k = delegationMapGhostHistoryView pre k

def eraseRangeBreakpoints {K : Type} [KeyTrait K] (entries : List (K × ID)) (lo hi : KeyIterator K) : List (K × ID) :=
  entries.filter (fun kv => !(keyIteratorBetween lo { k := some kv.1 } hi))

def insertSortedBreakpoint {K : Type} [KeyTrait K] [DecidableEq K] (key : K) (value : ID) : List (K × ID) → List (K × ID)
  | [] => [(key, value)]
  | (k, v) :: rest =>
      if key = k then
        (key, value) :: rest
      else if keyLtBool key k then
        (key, value) :: (k, v) :: rest
      else
        (k, v) :: insertSortedBreakpoint key value rest

def greatestLowerBoundIndexAux {K : Type} [KeyTrait K] (key : K) : List (K × ID) → Nat → Nat → Nat
  | [], _, best => best
  | (k, _) :: rest, idx, best =>
      if keyLeBool k key then greatestLowerBoundIndexAux key rest (idx + 1) idx else best

def greatestLowerBoundIndex {K : Type} [KeyTrait K] (entries : List (K × ID)) (key : K) : Nat :=
  greatestLowerBoundIndexAux key entries 0 0

def greatestLowerBoundIndexForIterator {K : Type} [KeyTrait K] (entries : List (K × ID)) : KeyIterator K → Nat
  | { k := some key } => greatestLowerBoundIndex entries key
  | { k := none } => entries.length - 1

def breakpointValuesAgreeInclusive {K : Type} (entries : List (K × ID)) (loIdx hiIdx : Nat) (dst : ID) : Bool :=
  ((entries.drop loIdx).take (hiIdx - loIdx + 1)).all (fun kv => ioTView kv.2 == ioTView dst)

def breakpointValuesAgreeBeforeHi {K : Type} (entries : List (K × ID)) (loIdx hiIdx : Nat) (dst : ID) : Bool :=
  ((entries.drop loIdx).take (hiIdx - loIdx)).all (fun kv => ioTView kv.2 == ioTView dst)

def iteratorMatchesBreakpointAt {K : Type} [DecidableEq K] (entries : List (K × ID)) (hi : KeyIterator K) (idx : Nat) : Bool :=
  match hi.k, entries[idx]? with
  | some hiK, some (k, _) => decide (k = hiK)
  | _, _ => false

namespace Bank

abbrev GetL1102Sig := {K : Type} → [KeyTrait K] → [DecidableEq K] → DelegationMap K → K → ID
abbrev SetL1115Sig := {K : Type} → [KeyTrait K] → [DecidableEq K] → DelegationMap K → KeyIterator K → KeyIterator K → ID → DelegationMap K
abbrev RangeConsistentImplSig := {K : Type} → [KeyTrait K] → [DecidableEq K] → DelegationMap K → KeyIterator K → KeyIterator K → ID → Bool
abbrev NewL1053Sig := {K : Type} → [KeyTrait K] → [DecidableEq K] → K → ID → DelegationMap K
abbrev DelegateForKeyRangeIsHostImplSig := DelegationMap CKey → KeyIterator AbstractKey → KeyIterator AbstractKey → ID → Bool

end Bank

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=get_l1102
-- !benchmark @end code_aux def=get_l1102

def Bank.get_l1102 : Bank.GetL1102Sig :=
-- !benchmark @start code def=get_l1102
  fun self k =>
    strictlyOrderedMapLookupWithDefault self.lows self.default k
-- !benchmark @end code def=get_l1102

-- !benchmark @start code_aux def=set_l1115
-- !benchmark @end code_aux def=set_l1115

def Bank.set_l1115 : Bank.SetL1115Sig :=
-- !benchmark @start code def=set_l1115
  fun self lo hi dst =>
    if keyIteratorLt lo hi then
      match lo.k with
      | none => self
      | some loK =>
          let erased := eraseRangeBreakpoints self.lows.m lo hi
          let restored :=
            match hi.k with
            | none => erased
            | some hiK =>
                let oldHi := strictlyOrderedMapLookupWithDefault self.lows self.default hiK
                insertSortedBreakpoint hiK oldHi erased
          let updated := insertSortedBreakpoint loK dst restored
          { self with
            lows := strictlyOrderedMapFromEntries updated,
            m := delegationGhostMapSetRange self.m lo hi dst,
            overrides := [],
            ranges := { lo := lo, hi := hi, dst := ioTView dst } :: self.ranges }
    else self
-- !benchmark @end code def=set_l1115

-- !benchmark @start code_aux def=range_consistent_impl
-- !benchmark @end code_aux def=range_consistent_impl

def Bank.range_consistent_impl : Bank.RangeConsistentImplSig :=
-- !benchmark @start code def=range_consistent_impl
  fun self lo hi dst =>
    if keyIteratorLt lo hi then
      match self.lows.m with
      | [] => false
      | entries =>
          let loIdx := greatestLowerBoundIndexForIterator entries lo
          let hiIdx := greatestLowerBoundIndexForIterator entries hi
          let agree := breakpointValuesAgreeInclusive entries loIdx hiIdx dst
          let almost := breakpointValuesAgreeBeforeHi entries loIdx hiIdx dst
          agree || (almost && iteratorMatchesBreakpointAt entries hi hiIdx)
    else true
-- !benchmark @end code def=range_consistent_impl

-- !benchmark @start code_aux def=new_l1053
-- !benchmark @end code_aux def=new_l1053

def Bank.new_l1053 : Bank.NewL1053Sig :=
-- !benchmark @start code def=new_l1053
  fun _ id =>
    { lows := strictlyOrderedMapFromEntries [(KeyTrait.zero_spec, id)],
      m := delegationGhostMapTotal (ioTView id),
      default := ioTView id,
      overrides := [],
      ranges := [] }
-- !benchmark @end code def=new_l1053

-- !benchmark @start code_aux def=delegate_for_key_range_is_host_impl
-- !benchmark @end code_aux def=delegate_for_key_range_is_host_impl

def Bank.delegate_for_key_range_is_host_impl : Bank.DelegateForKeyRangeIsHostImplSig :=
-- !benchmark @start code def=delegate_for_key_range_is_host_impl
  fun self lo hi dst =>
    Bank.range_consistent_impl self lo hi dst
-- !benchmark @end code def=delegate_for_key_range_is_host_impl
