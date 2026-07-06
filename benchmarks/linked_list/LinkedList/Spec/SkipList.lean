import LinkedList.Harness

/-!
# LinkedList.Spec.SkipList

Specifications for skip list (sorted association list) operations.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- Looking up any key in an empty skip list returns none. -/
def spec_skipl_find_empty (impl : RepoImpl) : Prop :=
  ∀ (k : Int), impl.linkedList.skipl_find [] k = none

/-- After inserting (k, v), looking up k returns some v. -/
def spec_skipl_find_insert_same (impl : RepoImpl) : Prop :=
  ∀ (s : List (Int × Int)) (k v : Int),
    impl.linkedList.skipl_find (impl.linkedList.skipl_insert s k v) k = some v

/-- Inserting under k1 does not affect lookups for a different key k2. -/
def spec_skipl_find_insert_different (impl : RepoImpl) : Prop :=
  ∀ (s : List (Int × Int)) (k1 k2 : Int) (v : Int), k1 ≠ k2 →
    impl.linkedList.skipl_find (impl.linkedList.skipl_insert s k1 v) k2
      = impl.linkedList.skipl_find s k2

/-- After deleting key k, looking up k returns none. -/
def spec_skipl_find_delete_same (impl : RepoImpl) : Prop :=
  ∀ (s : List (Int × Int)) (k : Int),
    impl.linkedList.skipl_find (impl.linkedList.skipl_delete s k) k = none

/-- Insert, lookup, and delete are consistent for the same key. -/
def spec_skipl_lookup_consistency (impl : RepoImpl) : Prop :=
  ∀ (s : List (Int × Int)) (k v : Int),
    impl.linkedList.skipl_find (impl.linkedList.skipl_insert s k v) k = some v ∧
    impl.linkedList.skipl_find
      (impl.linkedList.skipl_delete (impl.linkedList.skipl_insert s k v) k) k = none

/-- Deleting key k1 does not affect lookups for a different key k2. -/
def spec_skipl_find_delete_different (impl : RepoImpl) : Prop :=
  ∀ (s : List (Int × Int)) (k1 k2 : Int), k1 ≠ k2 →
    impl.linkedList.skipl_find (impl.linkedList.skipl_delete s k1) k2
      = impl.linkedList.skipl_find s k2
