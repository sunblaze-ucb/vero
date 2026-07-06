import Compression.Harness

/-!
# Compression.Spec.BurrowsWheeler

Specifications for Burrows-Wheeler Transform.  Each `spec_*` is a
property over an arbitrary `impl : RepoImpl`.

DO NOT MODIFY — this file is frozen curator-given content.
-/

/-- The `i`th cyclic rotation of a string. -/
def spec_bwt_helper_rotation (s : String) (i : Nat) : String :=
  String.ofList (s.toList.drop i ++ s.toList.take i)

/-- Exact model for enumerating all cyclic rotations in order. -/
def spec_bwt_helper_allRotationsModel (s : String) : List String :=
  (List.range s.length).map (spec_bwt_helper_rotation s)

/-- all_rotations produces exactly s.length rotation strings for every string s. -/
def spec_bwt_all_rotations_length (impl : RepoImpl) : Prop :=
  ∀ s : String, (impl.compression.all_rotations s).length = s.length

/-- all_rotations enumerates precisely the cyclic rotations, in index order. -/
def spec_bwt_all_rotations_exact (impl : RepoImpl) : Prop :=
  ∀ s : String,
    impl.compression.all_rotations s = spec_bwt_helper_allRotationsModel s

/-- Rotating the empty string returns an empty list. -/
def spec_bwt_all_rotations_empty (impl : RepoImpl) : Prop :=
  impl.compression.all_rotations "" = []

/-- Rotating a single-character string returns a singleton list containing that string. -/
def spec_bwt_all_rotations_singleton (impl : RepoImpl) : Prop :=
  ∀ c : Char,
    impl.compression.all_rotations (String.singleton c) = [String.singleton c]

/-- BWT of the empty string is the sentinel: bwt_string = "" and idx_original_string = 0. -/
def spec_bwt_transform_empty (impl : RepoImpl) : Prop :=
  let r := impl.compression.bwt_transform ""
  r.bwt_string = "" ∧ r.idx_original_string = 0

/-- The BWT output string has the same length as the input string. -/
def spec_bwt_transform_length_preserved (impl : RepoImpl) : Prop :=
  ∀ s : String, (impl.compression.bwt_transform s).bwt_string.length = s.length

/-- reverse_bwt of ("", 0) returns the empty string. -/
def spec_bwt_reverse_empty (impl : RepoImpl) : Prop :=
  impl.compression.reverse_bwt "" 0 = ""

/-- General round-trip: reversing the transform recovers the original string. -/
def spec_bwt_roundtrip (impl : RepoImpl) : Prop :=
  ∀ s : String,
    let r := impl.compression.bwt_transform s
    impl.compression.reverse_bwt r.bwt_string r.idx_original_string = s

/-- Canonical round-trip: BWT of "^BANANA|" then reverse_bwt recovers "^BANANA|". -/
def spec_bwt_roundtrip_canonical (impl : RepoImpl) : Prop :=
  let r := impl.compression.bwt_transform "^BANANA|"
  impl.compression.reverse_bwt r.bwt_string r.idx_original_string = "^BANANA|"

/-- Round-trip on "mississippi": transform then reverse_bwt recovers "mississippi". -/
def spec_bwt_roundtrip_mississippi (impl : RepoImpl) : Prop :=
  let r := impl.compression.bwt_transform "mississippi"
  impl.compression.reverse_bwt r.bwt_string r.idx_original_string = "mississippi"

/-- For every string, reversing its BWT transform recovers the original string. -/
def spec_bwt_roundtrip_all (impl : RepoImpl) : Prop :=
  ∀ s : String,
    let r := impl.compression.bwt_transform s
    impl.compression.reverse_bwt r.bwt_string r.idx_original_string = s
