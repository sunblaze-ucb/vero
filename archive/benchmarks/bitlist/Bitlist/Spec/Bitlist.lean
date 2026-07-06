import Bitlist.Harness

/-!
# Bitlist.Spec.Bitlist

Specifications for the `Bitlist` package. Each `spec_*` is a property
over an arbitrary `impl : RepoImpl`; specs access API functions via
`impl.bitlist.<fn>`.

DO NOT MODIFY — frozen curator-given content.
-/

/-- `make` is the identity wrapper: constructing a `Bitlist` from a `List Bool`
    returns exactly that list unchanged. Anchors that the bundle field wires
    correctly to the identity constructor. -/
def spec_make_identity (impl : RepoImpl) : Prop :=
  ∀ xs : List Bool, impl.bitlist.make xs = xs

/-- `length` after `make` equals the length of the underlying `List Bool`.
    Cross-API property tying `make` and `length` together; prevents a
    constant-returning `length` from passing. -/
def spec_length_matches_list (impl : RepoImpl) : Prop :=
  ∀ xs : List Bool,
    impl.bitlist.length (impl.bitlist.make xs) = xs.length

/-- The empty bitlist has length zero. Concrete edge-case pin for `length`. -/
def spec_length_empty (impl : RepoImpl) : Prop :=
  impl.bitlist.length [] = 0

/-- Concatenating two bitlists produces a bitlist whose length is the sum of
    the individual lengths. Confirms `add` is list-append and establishes
    `length` as a monoid morphism from `(Bitlist, add, [])` to `(Nat, +, 0)`. -/
def spec_add_length_distributes (impl : RepoImpl) : Prop :=
  ∀ a b : List Bool,
    impl.bitlist.length (impl.bitlist.add a b)
      = impl.bitlist.length a + impl.bitlist.length b

/-- The empty bitlist is a left identity for `add`. -/
def spec_add_empty_left (impl : RepoImpl) : Prop :=
  ∀ b : List Bool, impl.bitlist.add [] b = b

/-- The empty bitlist is a right identity for `add`. -/
def spec_add_empty_right (impl : RepoImpl) : Prop :=
  ∀ a : List Bool, impl.bitlist.add a [] = a

/-- `add` is associative. Together with the identity laws, this characterises
    `(Bitlist, add, [])` as a monoid. -/
def spec_add_associative (impl : RepoImpl) : Prop :=
  ∀ a b c : List Bool,
    impl.bitlist.add (impl.bitlist.add a b) c
      = impl.bitlist.add a (impl.bitlist.add b c)

/-- Converting the empty bitlist to an integer yields zero. -/
def spec_toInt_empty (impl : RepoImpl) : Prop :=
  impl.bitlist.bitlistToInt [] = 0

/-- A bitlist of `n` `false` bits converts to zero for any `n`.
    Generalises `spec_toInt_empty` (the `n = 0` case) and captures the
    all-zeros invariant universally. -/
def spec_toInt_all_zeros (impl : RepoImpl) : Prop :=
  ∀ n : Nat, impl.bitlist.bitlistToInt (List.replicate n false) = 0

/-- Concrete big-endian sanity check: the bit vector `1111011` equals 123.
    Matches the Python doctest `bitlist('1111011') = 123` and pins the
    big-endian convention. -/
def spec_toInt_concrete_123 (impl : RepoImpl) : Prop :=
  impl.bitlist.bitlistToInt [true, true, true, true, false, true, true] = 123

/-- Prepending a single `false` bit via `add` does not change the integer value.
    Captures "leading zeros are semantically zero" from the Python doctests;
    a strong cross-API invariant between `bitlistToInt` and `add`. -/
def spec_toInt_leading_zero_invariant (impl : RepoImpl) : Prop :=
  ∀ b : List Bool,
    impl.bitlist.bitlistToInt (impl.bitlist.add [false] b)
      = impl.bitlist.bitlistToInt b

/-- For any bitlist `b` of length `n`, its integer value is strictly less than
    `2 ^ n`. The universal "n-bit number fits in n bits" upper bound. -/
def spec_toInt_bounded (impl : RepoImpl) : Prop :=
  ∀ b : List Bool,
    impl.bitlist.bitlistToInt b < 2 ^ impl.bitlist.length b

/-- For a natural-number index `i` within bounds, `bitlist_getitem` returns the
    bit at that position. Uses `b.length` directly (valid since
    `Bitlist = List Bool` is an `abbrev`). -/
def spec_getitem_pos_in_range (impl : RepoImpl) : Prop :=
  ∀ (b : List Bool) (i : Nat) (h : i < b.length),
    impl.bitlist.bitlist_getitem b (Sum.inl (Int.ofNat i))
      = Except.ok (Sum.inl (b.get ⟨i, h⟩))

/-- For a natural-number index `i` at or beyond the length of `b`,
    `bitlist_getitem` returns an error value. -/
def spec_getitem_pos_out_of_range_errors (impl : RepoImpl) : Prop :=
  ∀ (b : List Bool) (i : Nat),
    i ≥ b.length →
    ∃ msg : String,
      impl.bitlist.bitlist_getitem b (Sum.inl (Int.ofNat i)) = Except.error msg

/-- The default full slice `(none, none, none)` returns the entire bitlist
    unchanged, wrapped in `Except.ok (Sum.inr _)`. Pins the identity behaviour
    of the default-bounds slice. -/
def spec_getitem_full_slice_returns_self (impl : RepoImpl) : Prop :=
  ∀ b : List Bool,
    impl.bitlist.bitlist_getitem b (Sum.inr (none, none, none))
      = Except.ok (Sum.inr b)

/-- For a non-empty bitlist `b`, index `-1` returns the last (least-significant)
    bit. Captures Python `b[-1]` semantics. -/
def spec_getitem_neg_one_is_last (impl : RepoImpl) : Prop :=
  ∀ (b : List Bool) (h : b ≠ []),
    impl.bitlist.bitlist_getitem b (Sum.inl (-1))
      = Except.ok (Sum.inl (b.getLast h))
