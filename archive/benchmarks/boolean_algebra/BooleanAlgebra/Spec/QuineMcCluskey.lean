import BooleanAlgebra.Harness

/-!
# BooleanAlgebra.Spec.QuineMcCluskey

Specifications for the Quine-McCluskey tabular minimization helpers.

DO NOT MODIFY — frozen curator-given content.
-/

/-- Comparing a string with itself returns `some s`. -/
def spec_compare_string_equal (impl : RepoImpl) : Prop :=
  ∀ s : String,
    impl.booleanAlgebra.compare_string s s = some s

/-- String comparison is symmetric: if `compare_string s1 s2 = some r` then `compare_string s2 s1 = some r`. -/
def spec_compare_string_symmetric (impl : RepoImpl) : Prop :=
  ∀ s1 s2 r : String,
    impl.booleanAlgebra.compare_string s1 s2 = some r →
    impl.booleanAlgebra.compare_string s2 s1 = some r

/-- Checking an empty list returns an empty list. -/
def spec_check_empty (impl : RepoImpl) : Prop :=
  impl.booleanAlgebra.check [] = []

/-- Checking a singleton list returns that list unchanged. -/
def spec_check_singleton (impl : RepoImpl) : Prop :=
  ∀ s : String, impl.booleanAlgebra.check [s] = [s]

/-- The output list has the same length as the input float list. -/
def spec_decimal_to_binary_length (impl : RepoImpl) : Prop :=
  ∀ n : Int, ∀ bits : List Float,
    (impl.booleanAlgebra.decimal_to_binary n bits).length = bits.length

/-- Every encoded minterm string has exactly `n.toNat` bits. -/
def spec_decimal_to_binary_width (impl : RepoImpl) : Prop :=
  ∀ n : Int, ∀ bits : List Float, ∀ out : String,
    out ∈ impl.booleanAlgebra.decimal_to_binary n bits →
    out.length = n.toNat

/-- A string covers itself exactly at difference count zero. -/
def spec_is_for_table_self (impl : RepoImpl) : Prop :=
  ∀ s : String, ∀ count : Int,
    impl.booleanAlgebra.is_for_table s s count = decide (count = 0)

/-- Coverage is symmetric in the implicant/minterm strings. -/
def spec_is_for_table_symmetric (impl : RepoImpl) : Prop :=
  ∀ s1 s2 : String, ∀ count : Int,
    impl.booleanAlgebra.is_for_table s1 s2 count =
      impl.booleanAlgebra.is_for_table s2 s1 count

/-- With no prime implicants, the prime implicant chart is empty. -/
def spec_prime_implicant_chart_empty_pis (impl : RepoImpl) : Prop :=
  ∀ mts : List String,
    impl.booleanAlgebra.prime_implicant_chart [] mts = []

/-- The chart has exactly one row per prime implicant. -/
def spec_prime_implicant_chart_length (impl : RepoImpl) : Prop :=
  ∀ pis mts : List String,
    (impl.booleanAlgebra.prime_implicant_chart pis mts).length = pis.length

/-- Every row in the chart has one entry per minterm. -/
def spec_prime_implicant_chart_row_lengths (impl : RepoImpl) : Prop :=
  ∀ pis mts : List String,
    ∀ row : List Int,
      row ∈ impl.booleanAlgebra.prime_implicant_chart pis mts →
      row.length = mts.length

/-- Chart entries are Boolean indicators encoded as 0 or 1. -/
def spec_prime_implicant_chart_entries_bool (impl : RepoImpl) : Prop :=
  ∀ pis mts : List String, ∀ row : List Int, ∀ v : Int,
    row ∈ impl.booleanAlgebra.prime_implicant_chart pis mts →
    v ∈ row →
    v = 0 ∨ v = 1

/-- A singleton chart row records exactly whether that implicant covers each minterm. -/
def spec_prime_implicant_chart_singleton_correct (impl : RepoImpl) : Prop :=
  ∀ pi : String, ∀ mts : List String,
    let count : Int := pi.toList.foldl (init := 0) fun a c => if c = '_' then a + 1 else a
    impl.booleanAlgebra.prime_implicant_chart [pi] mts =
      [mts.map fun mt => if impl.booleanAlgebra.is_for_table pi mt count then 1 else 0]

/-- With an empty coverage chart (no prime implicants), selection returns empty. -/
def spec_selection_empty (impl : RepoImpl) : Prop :=
  ∀ pis : List String,
    impl.booleanAlgebra.selection [] pis = []

/-- Selection only returns chosen prime implicants from the supplied list, except for
the implementation's out-of-range sentinel `""`. -/
def spec_selection_outputs_from_pis (impl : RepoImpl) : Prop :=
  ∀ chart : List (List Int), ∀ pis : List String, ∀ selected : String,
    selected ∈ impl.booleanAlgebra.selection chart pis →
    selected ∈ pis ∨ selected = ""
