import DedekindReals.Impl.Cut

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DedekindReals.Impl.Cauchy

Cauchy sequences of rational numbers and their embedding as Dedekind cuts.

DO NOT MODIFY types or signatures -- these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace DedekindReals

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- Frozen helpers translated from the Coq Cauchy development.

def CauchyQ (un : Nat → Rat) : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ n : Nat, ∀ i j : Nat, n ≤ i → n ≤ j → Rat.abs (un i - un j) < eps

def Un_cv_Q (un : Nat → Rat) (l : Rat) : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ n : Nat, ∀ i : Nat, n ≤ i → Rat.abs (un i - l) < eps

def CauchyQ_lower (un : Nat → Rat) (q : Rat) : Prop :=
  ∃ (r : Rat) (n : Nat), 0 < r ∧ ∀ i : Nat, n ≤ i → q + r < un i

def CauchyQ_upper (un : Nat → Rat) (q : Rat) : Prop :=
  ∃ (r : Rat) (n : Nat), 0 < r ∧ ∀ i : Nat, n ≤ i → un i < q - r

def sum_f_Q0 (f : Nat → Rat) : Nat → Rat
  | 0 => f 0
  | n + 1 => sum_f_Q0 f n + f (n + 1)

def Find_positive_in_sum : Prop :=
  ∀ (un : Nat → Rat) (n : Nat), (∀ k : Nat, 0 ≤ un k) →
    0 < sum_f_Q0 un n → ∃ k : Nat, 0 < un k

def sum_eq : Prop :=
  ∀ (un vn : Nat → Rat) (n : Nat), (∀ k : Nat, un k = vn k) →
    sum_f_Q0 un n = sum_f_Q0 vn n

def sum_Qle : Prop :=
  ∀ (un vn : Nat → Rat) (n : Nat), (∀ k : Nat, un k ≤ vn k) →
    sum_f_Q0 un n ≤ sum_f_Q0 vn n

def sum_assoc : Prop :=
  ∀ (u : Nat → Rat) (n p : Nat),
    sum_f_Q0 u ((n + 1) + p) =
      sum_f_Q0 u n + sum_f_Q0 (fun k => u ((n + 1) + k)) p

def cond_pos_sum : Prop :=
  ∀ (u : Nat → Rat) (n : Nat), (∀ k : Nat, 0 ≤ u k) → 0 ≤ sum_f_Q0 u n

def pos_sum_more : Prop :=
  ∀ (u : Nat → Rat) (n p : Nat), (∀ k : Nat, 0 ≤ u k) →
    n ≤ p → sum_f_Q0 u n ≤ sum_f_Q0 u p

def pos_sum_le_last : Prop :=
  ∀ (un : Nat → Rat) (n : Nat), (∀ k : Nat, 0 ≤ un k) →
    un n ≤ sum_f_Q0 un n

def multiTriangleIneg : Prop :=
  ∀ (u : Nat → Rat) (n : Nat),
    Rat.abs (sum_f_Q0 u n) ≤ sum_f_Q0 (fun k => Rat.abs (u k)) n

def Abs_sum_maj : Prop :=
  ∀ (un vn : Nat → Rat), (∀ n : Nat, Rat.abs (un n) ≤ vn n) →
    ∀ n p : Nat,
      Rat.abs (sum_f_Q0 un n - sum_f_Q0 un p) ≤
        sum_f_Q0 vn (Nat.max n p) - sum_f_Q0 vn (Nat.min n p)

def GeoHalfSum : Prop :=
  ∀ k : Nat, sum_f_Q0 (fun n : Nat => (1 / 2 : Rat) ^ n) k =
    2 - (1 / 2 : Rat) ^ k

def TwoPowerBound : Prop :=
  ∀ n : Nat, (n : Rat) < (2 : Rat) ^ n

def GeoHalfSeries : Prop :=
  Un_cv_Q (sum_f_Q0 (fun n : Nat => (1 / 2 : Rat) ^ n)) 2

-- API signatures

abbrev CauchyQRSig := (un : Nat → Rat) → CauchyQ un → R

end DedekindReals

-- Reference implementations

-- !benchmark @start code_aux def=CauchyQ_R
-- !benchmark @end code_aux def=CauchyQ_R

def DedekindReals.CauchyQ_R : DedekindReals.CauchyQRSig :=
-- !benchmark @start code def=CauchyQ_R
  fun un cau =>
    { lower := DedekindReals.CauchyQ_lower un
      upper := DedekindReals.CauchyQ_upper un
      lower_proper := by
        intro q r h
        cases h
        rfl
      upper_proper := by
        intro q r h
        cases h
        rfl
      lower_bound := by
        obtain ⟨n, hn⟩ := cau 1 (by grind)
        refine ⟨un n - 2, ?_⟩
        refine ⟨1, n, by grind, ?_⟩
        intro i hi
        have hni := hn n i (Nat.le_refl n) hi
        unfold Rat.abs at hni
        split at hni <;> grind
      upper_bound := by
        obtain ⟨n, hn⟩ := cau 1 (by grind)
        refine ⟨un n + 2, ?_⟩
        refine ⟨1, n, by grind, ?_⟩
        intro i hi
        have hni := hn n i (Nat.le_refl n) hi
        unfold Rat.abs at hni
        split at hni <;> grind
      lower_lower := by
        intro q r hqr h
        obtain ⟨s, n, hspos, hs⟩ := h
        refine ⟨s, n, hspos, ?_⟩
        intro i hi
        have hsi := hs i hi
        grind
      lower_open := by
        intro q h
        obtain ⟨s, n, hspos, hs⟩ := h
        refine ⟨q + s / 2, ?_, ?_⟩
        · grind
        · refine ⟨s / 2, n, ?_, ?_⟩
          · grind
          · intro i hi
            have hsi := hs i hi
            grind
      upper_upper := by
        intro q r hqr h
        obtain ⟨s, n, hspos, hs⟩ := h
        refine ⟨s, n, hspos, ?_⟩
        intro i hi
        have hsi := hs i hi
        grind
      upper_open := by
        intro q h
        obtain ⟨s, n, hspos, hs⟩ := h
        refine ⟨q - s / 2, ?_, ?_⟩
        · grind
        · refine ⟨s / 2, n, ?_, ?_⟩
          · grind
          · intro i hi
            have hsi := hs i hi
            grind
      disjoint := by
        intro q h
        obtain ⟨hl, hu⟩ := h
        obtain ⟨r, n, hrpos, hr⟩ := hl
        obtain ⟨s, m, hspos, hs⟩ := hu
        let k := Nat.max n m
        have hnk : n ≤ k := Nat.le_max_left n m
        have hmk : m ≤ k := Nat.le_max_right n m
        have hrl := hr k hnk
        have hsu := hs k hmk
        grind
      located := by
        intro q r hqr
        let eps : Rat := (r - q) / 4
        have heps : 0 < eps := by
          dsimp [eps]
          grind
        obtain ⟨n, hn⟩ := cau eps heps
        by_cases hlow : DedekindReals.CauchyQ_lower un q
        · exact Or.inl hlow
        · right
          have hnforall : ¬ ∀ i : Nat, n ≤ i → q + eps < un i := by
            intro hall
            exact hlow ⟨eps, n, heps, hall⟩
          have hex : ∃ i : Nat, n ≤ i ∧ ¬ q + eps < un i := by
            obtain ⟨i, hi⟩ := Classical.not_forall.mp hnforall
            exact ⟨i, Classical.not_imp.mp hi⟩
          obtain ⟨i, hi, hqi_not⟩ := hex
          have hqi_le : un i ≤ q + eps := by grind
          refine ⟨(r - q) / 2, n, ?_, ?_⟩
          · grind
          · intro j hj
            have hc := hn i j hi hj
            have h_upper : un j < un i + eps := by
              unfold Rat.abs at hc
              split at hc <;> grind
            dsimp [eps] at h_upper hqi_le
            grind }
-- !benchmark @end code def=CauchyQ_R
