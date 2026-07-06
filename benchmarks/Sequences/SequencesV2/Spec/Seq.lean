import SequencesV2.Harness

/-!
# SequencesV2.Spec.Seq

Frozen specifications for sequence operations translated from
`Collections/Sequences/Seq.dfy`. Each `spec_*` is a property over an
arbitrary `impl : RepoImpl`.

DO NOT MODIFY - this file is frozen curator-given content.
-/

open SequencesV2

/-- First returns the element at index 0 of a non-empty sequence. -/
def spec_Seq_First___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List T) (h : xs.length > 0),
    impl.sequences.Seq_First xs h = xs.get ⟨0, h⟩

/-- Dropping the last element and appending it reconstructs a non-empty sequence. -/
def spec_Seq_LemmaLast (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List T) (h : xs.length > 0), impl.sequences.Seq_DropLast xs h ++ [impl.sequences.Seq_Last xs h] = xs

/-- Last returns the element at index length - 1 of a non-empty sequence. -/
def spec_Seq_Last___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List T) (h : xs.length > 0),
    impl.sequences.Seq_Last xs h = xs.get ⟨xs.length - 1, Nat.sub_lt h (by decide)⟩

/-- Dropping the first element returns the suffix after index 0 and reconstructs the original with First. -/
def spec_Seq_DropFirst___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List T) (h : xs.length > 0),
    impl.sequences.Seq_DropFirst xs h = xs.drop 1 ∧
    [impl.sequences.Seq_First xs h] ++ impl.sequences.Seq_DropFirst xs h = xs

/-- The last element of xs ++ ys is the last element of non-empty ys. -/
def spec_Seq_LemmaAppendLast (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs ys : List T) (hys : ys.length > 0) (hcat : (xs ++ ys).length > 0), impl.sequences.Seq_Last (xs ++ ys) hcat = impl.sequences.Seq_Last ys hys

/-- Sequence concatenation is associative. -/
def spec_Seq_LemmaConcatIsAssociative (_impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs ys zs : List T), xs ++ (ys ++ zs) = (xs ++ ys) ++ zs

/-- Splitting a sequence at a valid position and concatenating the slices gives the original sequence. -/
def spec_Seq_LemmaSplitAt (_impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List T) (pos : Nat), pos < xs.length → Seq_Slice xs 0 pos ++ Seq_Slice xs pos xs.length = xs

/-- Elements of a valid slice agree with the corresponding original elements. -/
def spec_Seq_LemmaElementFromSlice (_impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs xs' : List T) (a b pos : Nat), a ≤ b → b ≤ xs.length → xs' = Seq_Slice xs a b → a ≤ pos → pos < b → pos - a < xs'.length ∧ xs'[pos - a]? = xs[pos]?

/-- A slice of a slice equals the corresponding direct slice of the original sequence. -/
def spec_Seq_LemmaSliceOfSlice (_impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List T) (s1 e1 s2 e2 : Nat), s1 ≤ e1 → e1 ≤ xs.length → s2 ≤ e2 → e2 ≤ e1 - s1 → Seq_Slice (Seq_Slice xs s1 e1) s2 e2 = Seq_Slice xs (s1 + s2) (s1 + e2)

/-- The set of elements of a sequence has cardinality at most the sequence length. -/
def spec_Seq_LemmaCardinalityOfSet (_impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (xs : List T), (Seq_ToSet xs).length ≤ xs.length

/-- Converting a sequence to a set is empty exactly when the sequence is empty. -/
def spec_Seq_LemmaCardinalityOfEmptySetIs0 (_impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (xs : List T), (Seq_ToSet xs).length = 0 ↔ xs.length = 0

/-- Concatenating two duplicate-free disjoint sequences preserves no-duplicates. -/
def spec_Seq_LemmaNoDuplicatesInConcat (_impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (xs ys : List T), Seq_HasNoDuplicates xs → Seq_HasNoDuplicates ys → Seq_Disjoint xs ys → Seq_HasNoDuplicates (xs ++ ys)

/-- A duplicate-free sequence has the same cardinality as its set of elements. -/
def spec_Seq_LemmaCardinalityOfSetNoDuplicates (_impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (xs : List T), Seq_HasNoDuplicates xs → (Seq_ToSet xs).length = xs.length

/-- If a sequence and its set of elements have the same cardinality, the sequence has no duplicates. -/
def spec_Seq_LemmaNoDuplicatesCardinalityOfSet (_impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (xs : List T), (Seq_ToSet xs).length = xs.length → Seq_HasNoDuplicates xs

/-- Each element of a duplicate-free sequence occurs exactly once. -/
def spec_Seq_LemmaMultisetHasNoDuplicates (_impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (xs : List T), Seq_HasNoDuplicates xs → ∀ x : T, x ∈ xs → Seq_Count x xs = 1

/-- ToArray preserves length and every element position. -/
def spec_Seq_ToArray___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List T),
    let arr := impl.sequences.Seq_ToArray xs
    arr.size = xs.length ∧
    ∀ i, i < xs.length → arr[i]? = xs[i]?

/-- IndexOf returns the first valid index containing the requested value. -/
def spec_Seq_IndexOf___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (xs : List T) (v : T) (h : v ∈ xs), let i := impl.sequences.Seq_IndexOf xs v h; i < xs.length ∧ xs[i]? = some v ∧ ∀ j, j < i → xs[j]? ≠ some v

/-- IndexOfOption returns the first index when present and none exactly when absent. -/
def spec_Seq_IndexOfOption___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (xs : List T) (v : T), match impl.sequences.Seq_IndexOfOption xs v with | some i => i < xs.length ∧ xs[i]? = some v ∧ ∀ j, j < i → xs[j]? ≠ some v | none => v ∉ xs

/-- LastIndexOf returns the last valid index containing the requested value. -/
def spec_Seq_LastIndexOf___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (xs : List T) (v : T) (h : v ∈ xs), let i := impl.sequences.Seq_LastIndexOf xs v h; i < xs.length ∧ xs[i]? = some v ∧ ∀ j, i < j → j < xs.length → xs[j]? ≠ some v

/-- LastIndexOfOption returns the last index when present and none exactly when absent. -/
def spec_Seq_LastIndexOfOption___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (xs : List T) (v : T), match impl.sequences.Seq_LastIndexOfOption xs v with | some i => i < xs.length ∧ xs[i]? = some v ∧ ∀ j, i < j → j < xs.length → xs[j]? ≠ some v | none => v ∉ xs

/-- Removing at a valid position shortens the sequence and preserves surrounding elements. -/
def spec_Seq_Remove___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List T) (pos : Nat) (h : pos < xs.length), let ys := impl.sequences.Seq_Remove xs pos h; ys.length = xs.length - 1 ∧ (∀ i, i < pos → ys[i]? = xs[i]?) ∧ (∀ i, pos ≤ i → i < xs.length - 1 → ys[i]? = xs[i + 1]?)

/-- RemoveValue leaves absent values unchanged and removes one occurrence when present. -/
def spec_Seq_RemoveValue___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (xs : List T) (v : T),
    let ys := impl.sequences.Seq_RemoveValue xs v
    ys = xs.erase v ∧
      (v ∉ xs → ys = xs) ∧
      (v ∈ xs → Seq_Count v ys + 1 = Seq_Count v xs) ∧
      (∀ x : T, x ≠ v → Seq_Count x ys = Seq_Count x xs) ∧
      (Seq_HasNoDuplicates xs → Seq_HasNoDuplicates ys ∧ Seq_ToSet ys = (Seq_ToSet xs).filter (fun x => x ≠ v))

/-- Insert adds an element at the requested position and preserves the multiset. -/
def spec_Seq_Insert___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} [DecidableEq T] (xs : List T) (a : T) (pos : Nat) (h : pos ≤ xs.length), let ys := impl.sequences.Seq_Insert xs a pos h; ys.length = xs.length + 1 ∧ (∀ i, i < pos → ys[i]? = xs[i]?) ∧ (∀ i, pos ≤ i → i < xs.length → ys[i + 1]? = xs[i]?) ∧ ys[pos]? = some a ∧ Seq_SameMultiset ys (xs ++ [a])

/-- Reverse has the same length and mirrors element positions. -/
def spec_Seq_Reverse___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List T), let ys := impl.sequences.Seq_Reverse xs; ys.length = xs.length ∧ ∀ i, i < xs.length → ys[i]? = xs[xs.length - i - 1]?

/-- Repeat creates a constant sequence of the requested length. -/
def spec_Seq_Repeat___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (v : T) (length : Nat), let xs := impl.sequences.Seq_Repeat v length; xs.length = length ∧ ∀ i, i < xs.length → xs[i]? = some v

/-- Unzip produces equal-length component sequences that reconstruct each source pair. -/
def spec_Seq_Unzip___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {A B : Type} (xs : List (A × B)), let r := impl.sequences.Seq_Unzip xs; r.1.length = xs.length ∧ r.2.length = xs.length ∧ ∀ i, i < xs.length → match r.1[i]?, r.2[i]?, xs[i]? with | some a, some b, some p => (a, b) = p | _, _, _ => False

/-- Zip creates pair elements and unzipping the result recovers the inputs. -/
def spec_Seq_Zip___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {A B : Type} (xs : List A) (ys : List B) (h : xs.length = ys.length), let zs := impl.sequences.Seq_Zip xs ys h; zs.length = xs.length ∧ (∀ i, i < zs.length → zs[i]? = match xs[i]?, ys[i]? with | some x, some y => some (x, y) | _, _ => none) ∧ (impl.sequences.Seq_Unzip zs).1 = xs ∧ (impl.sequences.Seq_Unzip zs).2 = ys

/-- Unzipping and then zipping a sequence of pairs recovers the original sequence. -/
def spec_Seq_LemmaZipOfUnzip (impl : RepoImpl) : Prop :=
  ∀ {A B : Type} (xs : List (A × B)) (h : (impl.sequences.Seq_Unzip xs).1.length = (impl.sequences.Seq_Unzip xs).2.length), impl.sequences.Seq_Zip (impl.sequences.Seq_Unzip xs).1 (impl.sequences.Seq_Unzip xs).2 h = xs

/-- Max returns an element of the non-empty sequence that is at least every element. -/
def spec_Seq_Max___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ (xs : List Int) (h : xs.length > 0), let m := impl.sequences.Seq_Max xs h; (∀ k, k ∈ xs → k ≤ m) ∧ m ∈ xs

/-- The maximum of a concatenation is at least the maximum of each non-empty side and all elements. -/
def spec_Seq_LemmaMaxOfConcat (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Int) (hx : xs.length > 0) (hy : ys.length > 0) (hcat : (xs ++ ys).length > 0), impl.sequences.Seq_Max (xs ++ ys) hcat ≥ impl.sequences.Seq_Max xs hx ∧ impl.sequences.Seq_Max (xs ++ ys) hcat ≥ impl.sequences.Seq_Max ys hy ∧ ∀ i, i ∈ xs ++ ys → i ≤ impl.sequences.Seq_Max (xs ++ ys) hcat

/-- Min returns an element of the non-empty sequence that is at most every element. -/
def spec_Seq_Min___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ (xs : List Int) (h : xs.length > 0), let m := impl.sequences.Seq_Min xs h; (∀ k, k ∈ xs → m ≤ k) ∧ m ∈ xs

/-- The minimum of a concatenation is at most the minimum of each non-empty side and all elements. -/
def spec_Seq_LemmaMinOfConcat (impl : RepoImpl) : Prop :=
  ∀ (xs ys : List Int) (hx : xs.length > 0) (hy : ys.length > 0) (hcat : (xs ++ ys).length > 0), impl.sequences.Seq_Min (xs ++ ys) hcat ≤ impl.sequences.Seq_Min xs hx ∧ impl.sequences.Seq_Min (xs ++ ys) hcat ≤ impl.sequences.Seq_Min ys hy ∧ ∀ i, i ∈ xs ++ ys → impl.sequences.Seq_Min (xs ++ ys) hcat ≤ i

/-- The maximum of a non-empty slice is bounded by the maximum of the full non-empty sequence. -/
def spec_Seq_LemmaSubseqMax (impl : RepoImpl) : Prop :=
  ∀ (xs : List Int) (lo hi : Nat) (_hsub : lo < hi ∧ hi ≤ xs.length) (hall : xs.length > 0) (hslice : (Seq_Slice xs lo hi).length > 0), impl.sequences.Seq_Max (Seq_Slice xs lo hi) hslice ≤ impl.sequences.Seq_Max xs hall

/-- The minimum of a non-empty slice is bounded below by the minimum of the full non-empty sequence. -/
def spec_Seq_LemmaSubseqMin (impl : RepoImpl) : Prop :=
  ∀ (xs : List Int) (lo hi : Nat) (_hsub : lo < hi ∧ hi ≤ xs.length) (hall : xs.length > 0) (hslice : (Seq_Slice xs lo hi).length > 0), impl.sequences.Seq_Min (Seq_Slice xs lo hi) hslice ≥ impl.sequences.Seq_Min xs hall

/-- Flatten returns the source-order concatenation of all component sequences. -/
def spec_Seq_Flatten___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List (List T)),
    impl.sequences.Seq_Flatten xs = xs.flatten

/-- FlattenReverse computes the same source-order flattened sequence by recursing from the right. -/
def spec_Seq_FlattenReverse___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List (List T)),
    impl.sequences.Seq_FlattenReverse xs = xs.flatten

/-- Flatten distributes over sequence concatenation. -/
def spec_Seq_LemmaFlattenConcat (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs ys : List (List T)), impl.sequences.Seq_Flatten (xs ++ ys) = impl.sequences.Seq_Flatten xs ++ impl.sequences.Seq_Flatten ys

/-- Reverse-order flattening distributes over sequence concatenation. -/
def spec_Seq_LemmaFlattenReverseConcat (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs ys : List (List T)), impl.sequences.Seq_FlattenReverse (xs ++ ys) = impl.sequences.Seq_FlattenReverse xs ++ impl.sequences.Seq_FlattenReverse ys

/-- Left-to-right and right-to-left flattening produce the same flattened sequence. -/
def spec_Seq_LemmaFlattenAndFlattenReverseAreEquivalent (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List (List T)), impl.sequences.Seq_Flatten xs = impl.sequences.Seq_FlattenReverse xs

/-- The flattened length is at least the length of any component sequence. -/
def spec_Seq_LemmaFlattenLengthGeSingleElementLength (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List (List T)) (i : Nat), i < xs.length → match xs[i]? with | some x => x.length ≤ (impl.sequences.Seq_FlattenReverse xs).length | none => False

/-- The flattened length is bounded by the number of sequences times a uniform component-length bound. -/
def spec_Seq_LemmaFlattenLengthLeMul (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (xs : List (List T)) (j : Nat), (∀ (i : Nat) (x : List T), xs[i]? = some x → x.length ≤ j) → (impl.sequences.Seq_FlattenReverse xs).length ≤ xs.length * j

/-- FlatMap is the optimized implementation of Flatten(Map f xs). -/
def spec_Seq_FlatMap___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T R : Type} (f : T → List R) (xs : List T),
    impl.sequences.Seq_FlatMap f xs = xs.flatMap f ∧
      impl.sequences.Seq_FlatMap f xs =
        impl.sequences.Seq_Flatten (impl.sequences.Seq_Map f xs)

/-- Map preserves length and applies the function pointwise. -/
def spec_Seq_Map___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T R : Type} (f : T → R) (xs : List T), let result := impl.sequences.Seq_Map f xs; result.length = xs.length ∧ ∀ i, i < xs.length → result[i]? = Option.map f xs[i]?

/-- MapWithResult succeeds pointwise or returns a failure produced by some input element. -/
def spec_Seq_MapWithResult___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T R E : Type} (f : T → Result R E) (xs : List T),
    match impl.sequences.Seq_MapWithResult f xs with
    | Result.Success result =>
        result.length = xs.length ∧
          ∀ i, i < xs.length → ∃ v, f <$> xs[i]? = some (Result.Success v) ∧ result[i]? = some v
    | Result.Failure e =>
        ∃ i, i < xs.length ∧
          f <$> xs[i]? = some (Result.Failure e) ∧
          ∀ j, j < i → ∃ v, f <$> xs[j]? = some (Result.Success v)

/-- Map distributes over sequence concatenation. -/
def spec_Seq_LemmaMapDistributesOverConcat (impl : RepoImpl) : Prop :=
  ∀ {T R : Type} (f : T → R) (xs ys : List T), impl.sequences.Seq_Map f (xs ++ ys) = impl.sequences.Seq_Map f xs ++ impl.sequences.Seq_Map f ys

/-- Filter returns exactly the source-order subsequence satisfying the predicate. -/
def spec_Seq_Filter___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (f : T → Bool) (xs : List T),
    impl.sequences.Seq_Filter f xs = xs.filter f

/-- Filter distributes over sequence concatenation. -/
def spec_Seq_LemmaFilterDistributesOverConcat (impl : RepoImpl) : Prop :=
  ∀ {T : Type} (f : T → Bool) (xs ys : List T), impl.sequences.Seq_Filter f (xs ++ ys) = impl.sequences.Seq_Filter f xs ++ impl.sequences.Seq_Filter f ys

/-- FoldLeft is the ordinary left fold over the input sequence. -/
def spec_Seq_FoldLeft___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {A T : Type} (f : A → T → A) (init : A) (xs : List T),
    impl.sequences.Seq_FoldLeft f init xs = xs.foldl f init

/-- FoldLeft over concatenation equals folding the left side then the right side. -/
def spec_Seq_LemmaFoldLeftDistributesOverConcat (impl : RepoImpl) : Prop :=
  ∀ {A T : Type} (f : A → T → A) (init : A) (xs ys : List T), impl.sequences.Seq_FoldLeft f init (xs ++ ys) = impl.sequences.Seq_FoldLeft f (impl.sequences.Seq_FoldLeft f init xs) ys

/-- A left-fold invariant is preserved through FoldLeft. -/
def spec_Seq_LemmaInvFoldLeft (impl : RepoImpl) : Prop :=
  ∀ {A B : Type} (inv : B → List A → Prop) (stp : B → A → B → Prop) (f : B → A → B) (b : B) (xs : List A), Seq_InvFoldLeft inv stp → (∀ b a, stp b a (f b a)) → inv b xs → inv (impl.sequences.Seq_FoldLeft f b xs) []

/-- FoldRight is the ordinary right fold over the input sequence. -/
def spec_Seq_FoldRight___ensures_spec (impl : RepoImpl) : Prop :=
  ∀ {A T : Type} (f : T → A → A) (xs : List T) (init : A),
    impl.sequences.Seq_FoldRight f xs init = xs.foldr f init

/-- FoldRight over concatenation folds the right side into the initial accumulator and then folds the left side. -/
def spec_Seq_LemmaFoldRightDistributesOverConcat (impl : RepoImpl) : Prop :=
  ∀ {A T : Type} (f : T → A → A) (init : A) (xs ys : List T), impl.sequences.Seq_FoldRight f (xs ++ ys) init = impl.sequences.Seq_FoldRight f xs (impl.sequences.Seq_FoldRight f ys init)

/-- A right-fold invariant is preserved through FoldRight. -/
def spec_Seq_LemmaInvFoldRight (impl : RepoImpl) : Prop :=
  ∀ {A B : Type} (inv : List A → B → Prop) (stp : A → B → B → Prop) (f : A → B → B) (b : B) (xs : List A), Seq_InvFoldRight inv stp → (∀ a b, stp a b (f a b)) → inv [] b → inv xs (impl.sequences.Seq_FoldRight f xs b)
