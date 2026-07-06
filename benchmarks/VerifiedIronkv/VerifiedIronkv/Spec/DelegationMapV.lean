import VerifiedIronkv.Harness

/-!
# VerifiedIronkv.Spec.DelegationMapV

Frozen specifications for `DelegationMapV`.

DO NOT MODIFY — curator-given content.
-/

/-- `DelegationMap.new` returns a valid map whose total view maps every key to the initial endpoint, matching the source `Map::total` postcondition. -/
def spec_delegation_map_new_total_default (impl : RepoImpl) : Prop :=
  ∀ {K : Type} [KeyTrait K] [DecidableEq K] (k : K) (id : ID), k = (KeyTrait.zero_spec : K) → impl.verifiedIronkv.valid_physical_address id = true → delegationMapNewTotalDefault (impl.verifiedIronkv.new_l1053 k id) id

/-- For a source-valid delegation map, `get_l1102` returns an endpoint whose view matches both the breakpoint model and the approved ghost-map representation, and is physically valid. -/
def spec_delegation_map_get_refines_view (impl : RepoImpl) : Prop :=
  ∀ {K : Type} [KeyTrait K] [DecidableEq K] (self : DelegationMap K) (k : K), delegationMapSourceValid self →
    ioTView (impl.verifiedIronkv.get_l1102 self k) = view_L1038 self k ∧
    impl.verifiedIronkv.valid_physical_address (impl.verifiedIronkv.get_l1102 self k) = true ∧
    ioTView (impl.verifiedIronkv.get_l1102 self k) = delegationMapSourceGhostViewOf self k ∧
    (∀ ghostView : K → AbstractEndPoint,
      delegationMapSourceGhostView self ghostView →
        ioTView (impl.verifiedIronkv.get_l1102 self k) = ghostView k)

/-- `set_l1115` preserves validity and updates exactly the selected key range in the approved ghost-map representation. -/
def spec_delegation_map_set_updates_range (impl : RepoImpl) : Prop :=
  ∀ {K : Type} [KeyTrait K] [LawfulKeyTrait K] [DecidableEq K] (self : DelegationMap K) (lo hi : KeyIterator K) (dst : ID), delegationMapSourceValid self → impl.verifiedIronkv.valid_physical_address dst = true →
    let post := impl.verifiedIronkv.set_l1115 self lo hi dst
    delegationMapValid post = true ∧
    delegationMapSetUpdatesRange self post lo hi dst ∧
    (if keyIteratorLt lo hi then
      delegationMapSourceValid post ∧
      delegationMapGhostHistorySetUpdateBridge self post lo hi dst ∧
      (∀ preGhost postGhost : K → AbstractEndPoint,
        delegationMapSourceGhostView self preGhost →
        delegationMapSourceGhostView post postGhost →
          delegationMapSourceGhostSetUpdate self post preGhost postGhost lo hi dst)
    else
      post.ranges = self.ranges)

/-- `range_consistent_impl` returns true exactly when range consistency holds in the approved ghost-map representation. -/
def spec_range_consistent_impl_iff_range_consistent (impl : RepoImpl) : Prop :=
  ∀ {K : Type} [KeyTrait K] [LawfulKeyTrait K] [DecidableEq K] (self : DelegationMap K) (lo hi : KeyIterator K) (dst : ID), delegationMapSourceValid self →
    (impl.verifiedIronkv.range_consistent_impl self lo hi dst = true ↔ delegationMapRangeConsistent self lo hi dst) ∧
    (impl.verifiedIronkv.range_consistent_impl self lo hi dst = true ↔
      delegationMapGhostRangeConsistent (delegationMapSourceGhostViewOf self) lo hi dst) ∧
    (∀ ghostView : K → AbstractEndPoint,
      delegationMapSourceGhostView self ghostView →
        (impl.verifiedIronkv.range_consistent_impl self lo hi dst = true ↔
          delegationMapGhostRangeConsistent ghostView lo hi dst))

/-- `delegate_for_key_range_is_host_impl` agrees with the abstract delegation-map protocol predicate for the selected key range. -/
def spec_delegate_for_key_range_is_host_impl_matches_protocol (impl : RepoImpl) : Prop :=
  ∀ (self : DelegationMap CKey) (lo hi : KeyIterator AbstractKey) (dst : ID), delegationMapSourceValid self →
    (impl.verifiedIronkv.delegate_for_key_range_is_host_impl self lo hi dst = true ↔ abstractDelegationMapDelegateForKeyRangeIsHostModel self { lo := lo, hi := hi } (ioTView dst)) ∧
    (impl.verifiedIronkv.delegate_for_key_range_is_host_impl self lo hi dst = true ↔
      delegationMapGhostRangeConsistent (delegationMapSourceGhostViewOf self) lo hi dst)
