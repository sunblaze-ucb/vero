import JsonV2.Harness

/-!
# Json.Spec.Utils.Vectors

Frozen specifications for vector behavior from `JSON.Utils.Vectors`.
-/

open JSON

/-- Vector put updates items. -/
def spec_vector_put_updates_items (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α) (idx : UInt32) (a : α),
    idx.toNat < v.items.length →
    (impl.json.vector_Put v idx a).items = v.items.set idx.toNat a

/-- Vector put preserves capacity. -/
def spec_vector_put_preserves_capacity (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α) (idx : UInt32) (a : α),
    (impl.json.vector_Put v idx a).capacity = v.capacity

/-- Under the Dafny Realloc precondition new_capacity > capacity, vector_Realloc succeeds and updates capacity. -/
def spec_vector_realloc_ok_updates_capacity (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α) (new_cap : UInt32),
    v.capacity < new_cap.toNat →
    impl.json.vector_Realloc v new_cap = .ok { v with capacity := new_cap.toNat }

/-- Vector realloc default oom iff max. -/
def spec_vector_realloc_default_oom_iff_max (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α),
    impl.json.vector_ReallocDefault v = .error .outOfMemory ↔ v.capacity = 2 ^ 32 - 1

/-- Vector realloc default ok grows. -/
def spec_vector_realloc_default_ok_grows (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α) (v' : JVector α),
    impl.json.vector_ReallocDefault v = .ok v' →
    v'.capacity > v.capacity

/-- Vector ensure ok has space. -/
def spec_vector_ensure_ok_has_space (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α) (reserved : UInt32) (v' : JVector α),
    impl.json.vector_Ensure v reserved = .ok v' →
    v'.items.length + reserved.toNat ≤ v'.capacity

/-- Vector ensure fail overflow. -/
def spec_vector_ensure_fail_overflow (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α) (reserved : UInt32),
    v.items.length + reserved.toNat > 2 ^ 32 - 1 →
    impl.json.vector_Ensure v reserved = .error .outOfMemory

/-- Vector pop fast removes last. -/
def spec_vector_pop_fast_removes_last (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α),
    (impl.json.vector_PopFast v).items = v.items.dropLast

/-- Vector pop fast preserves capacity. -/
def spec_vector_pop_fast_preserves_capacity (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α),
    (impl.json.vector_PopFast v).capacity = v.capacity

/-- Vector push fast appends. -/
def spec_vector_push_fast_appends (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α) (a : α),
    (impl.json.vector_PushFast v a).items = v.items ++ [a]

/-- Vector push fast preserves capacity. -/
def spec_vector_push_fast_preserves_capacity (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α) (a : α),
    (impl.json.vector_PushFast v a).capacity = v.capacity

/-- Vector push ok appends. -/
def spec_vector_push_ok_appends (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α) (a : α) (v' : JVector α),
    impl.json.vector_Push v a = .ok v' →
    v'.items = v.items ++ [a]

/-- Vector push fail oom. -/
def spec_vector_push_fail_oom (impl : RepoImpl) : Prop :=
  ∀ {α : Type} (v : JVector α) (a : α),
    impl.json.vector_Push v a = .error .outOfMemory →
    v.capacity = 2 ^ 32 - 1
