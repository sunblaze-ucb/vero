import Flocq.IEEE754.Spec.Bits
import Flocq.IEEE754.Spec.PrimFloat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-! Curator-only kernel regressions. From `benchmarks/Flocq`, run
    `lake env lean ../../tests/lean/flocq_contracts.lean`.
    No native evaluation or conversion axioms are used in these proofs. -/

namespace Flocq.ContractTests

private theorem split_join (mw ew : Nat) (s : Bool) (e m : Int)
    (he : 0 ≤ e ∧ e < (2 : Int) ^ ew) (hm : 0 ≤ m ∧ m < (2 : Int) ^ mw) :
    _root_.splitBits mw ew (joinBits mw ew s e m) = (s, e, m) := by
  have hp : 0 < (2 : Int) ^ mw := pow_pos (by decide) _
  have hq : 0 < (2 : Int) ^ ew := pow_pos (by decide) _
  have hdiv := Int.ediv_eq_zero_of_lt hm.1 hm.2
  have hmod := Int.emod_eq_of_lt hm.1 hm.2
  have hemod := Int.emod_eq_of_lt he.1 he.2
  unfold _root_.splitBits joinBits
  rw [pow_add]
  cases s <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · simp only [zero_add, Int.mul_add_ediv_right _ _ (ne_of_gt hp), hdiv, add_zero,
      Int.mul_add_emod_self_right, hmod, hemod]
    have : ¬ (2 : Int) ^ mw * 2 ^ ew ≤ e * 2 ^ mw + m := by nlinarith
    simp [this]
  · have hrewrite : (2 : Int) ^ mw * 2 ^ ew + e * 2 ^ mw + m =
        (2 ^ ew + e) * 2 ^ mw + m := by ring
    rw [hrewrite]
    simp only [Int.mul_add_ediv_right _ _ (ne_of_gt hp), hdiv, add_zero,
      hmod, Int.add_emod, Int.emod_self, zero_add,
      Int.emod_emod, hemod]
    have : (2 : Int) ^ mw * 2 ^ ew ≤ (2 ^ ew + e) * 2 ^ mw + m := by nlinarith
    simp [this, hmod]

private theorem pow_next (n : Int) (hn : 0 ≤ n) :
    (2 : Int) ^ (n + 1).toNat = 2 * (2 : Int) ^ n.toNat := by
  rw [show (n + 1).toNat = n.toNat + 1 by omega, pow_succ]
  ring

private theorem exponent_width {mw ew : Int} (h : validBitFormat mw ew) :
    (2 : Int) ^ ew.toNat = 2 * (2 : Int) ^ (ew - 1).toNat := by
  simpa using pow_next (ew - 1) (by rcases h with ⟨_, he, _⟩; omega)

private theorem decode_valid {mw ew : Int} (h : validBitFormat mw ew) (n : Int) :
    _root_.validBinary _ _ (_root_.binaryFloatOfBitsAux mw ew n) = true := by
  have hp : 0 < (2 : Int) ^ mw.toNat := pow_pos (by decide) _
  have hq : 0 < (2 : Int) ^ ew.toNat := pow_pos (by decide) _
  have hm0 := Int.emod_nonneg n (ne_of_gt hp)
  have hm1 := Int.emod_lt_of_pos n hp
  have he0 := Int.emod_nonneg (n / (2 : Int) ^ mw.toNat) (ne_of_gt hq)
  have he1 := Int.emod_lt_of_pos (n / (2 : Int) ^ mw.toNat) hq
  have hwidth := exponent_width h
  have hprec := pow_next mw (by rcases h with ⟨hm, _, _⟩; omega)
  have hmax := h.2.2
  have hmw := h.1
  have hmnat := Int.toNat_of_nonneg hm0
  have hnorm := Int.toNat_of_nonneg (show 0 ≤ n % (2 : Int) ^ mw.toNat + 2 ^ mw.toNat by omega)
  unfold _root_.binaryFloatOfBitsAux _root_.splitBits
  dsimp only
  split_ifs <;> simp only [_root_.validBinary, decide_eq_true_eq]
  all_goals simp only [Int.add_sub_cancel, hmnat, hnorm]
  all_goals try simp only [hprec]
  all_goals omega

private theorem encode_decode_fields (mw ew : Int)
    (n : Int) (s : Bool) (e m : Int)
    (hs : _root_.splitBits mw.toNat ew.toNat n = (s, e, m))
    (hm : 0 ≤ m ∧ m < (2 : Int) ^ mw.toNat) :
    Flocq.bitsOfBinaryFloat mw ew (_root_.binaryFloatOfBitsAux mw ew n) =
      joinBits mw.toNat ew.toNat s e m := by
  have hp : 0 < (2 : Int) ^ mw.toNat := pow_pos (by decide) _
  have hmnat := Int.toNat_of_nonneg hm.1
  have hnorm := Int.toNat_of_nonneg (show 0 ≤ m + (2 : Int) ^ mw.toNat by omega)
  have hew : ew.toNat - 1 = (ew - 1).toNat := by omega
  simp only [_root_.binaryFloatOfBitsAux, hs]
  split_ifs <;> simp only [Flocq.bitsOfBinaryFloat, joinBits, hmnat, hnorm, hew]
  all_goals split_ifs <;> simp_all <;> ring

private theorem decode_encode {mw ew : Int} (h : validBitFormat mw ew)
    (x : BinaryFloat (mw + 1) ((2 : Int) ^ (ew - 1).toNat))
    (hx : _root_.validBinary _ _ x = true) :
    _root_.binaryFloatOfBitsAux mw ew (Flocq.bitsOfBinaryFloat mw ew x) = x := by
  have hp : 0 < (2 : Int) ^ mw.toNat := pow_pos (by decide) _
  have hwidth := exponent_width h
  have hprec := pow_next mw (by rcases h with ⟨hm, _, _⟩; omega)
  have hmax := h.2.2
  have hmw := h.1
  have hq : 1 < (2 : Int) ^ ew.toNat := by omega
  have hew : ew.toNat - 1 = (ew - 1).toNat := by omega
  cases x with
  | zero s =>
    rw [show Flocq.bitsOfBinaryFloat mw ew (.zero s) =
      joinBits mw.toNat ew.toNat s 0 0 by simp [Flocq.bitsOfBinaryFloat, joinBits]]
    simp only [_root_.binaryFloatOfBitsAux,
      split_join mw.toNat ew.toNat s 0 0 (by omega) (by omega)]
    simp
  | inf s =>
    rw [show Flocq.bitsOfBinaryFloat mw ew (.inf s) =
      joinBits mw.toNat ew.toNat s ((2 : Int) ^ ew.toNat - 1) 0 by
        simp [Flocq.bitsOfBinaryFloat, joinBits]]
    simp only [_root_.binaryFloatOfBitsAux,
      split_join mw.toNat ew.toNat s ((2 : Int) ^ ew.toNat - 1) 0 (by omega) (by omega)]
    simp [show (2 : Int) ^ ew.toNat - 1 ≠ 0 by omega]
  | nan s pl =>
    simp only [_root_.validBinary, Int.add_sub_cancel, decide_eq_true_eq] at hx
    change _root_.binaryFloatOfBitsAux mw ew
      (joinBits mw.toNat ew.toNat s ((2 : Int) ^ ew.toNat - 1) pl) = _
    simp only [_root_.binaryFloatOfBitsAux,
      split_join mw.toNat ew.toNat s ((2 : Int) ^ ew.toNat - 1) pl (by omega) (by omega)]
    simp [show (2 : Int) ^ ew.toNat - 1 ≠ 0 by omega, show pl ≠ 0 by omega]
  | finite s m e =>
    simp only [_root_.validBinary, Int.add_sub_cancel, decide_eq_true_eq, hprec] at hx
    by_cases hm : (2 : Int) ^ mw.toNat ≤ (m : Int)
    · have hmfield : 0 ≤ (m : Int) - (2 : Int) ^ mw.toNat ∧
          (m : Int) - (2 : Int) ^ mw.toNat < (2 : Int) ^ mw.toNat := by omega
      have hefield : 0 ≤ e - (2 - (2 : Int) ^ (ew - 1).toNat - mw) + 1 ∧
          e - (2 - (2 : Int) ^ (ew - 1).toNat - mw) + 1 < (2 : Int) ^ ew.toNat := by omega
      have hn : 0 ≤ (m : Int) - (2 : Int) ^ mw.toNat := by omega
      simp only [Flocq.bitsOfBinaryFloat, hew, if_pos hn]
      change _root_.binaryFloatOfBitsAux mw ew (joinBits mw.toNat ew.toNat s _ _) = _
      simp only [_root_.binaryFloatOfBitsAux, split_join _ _ _ _ _ hefield hmfield]
      have he0 : e - (2 - (2 : Int) ^ (ew - 1).toNat - mw) + 1 ≠ 0 := by omega
      have hemax : e - (2 - (2 : Int) ^ (ew - 1).toNat - mw) + 1 ≠
          (2 : Int) ^ ew.toNat - 1 := by omega
      simp only [if_neg he0, if_neg hemax]
      congr 1 <;> omega
    · have hn : ¬ 0 ≤ (m : Int) - (2 : Int) ^ mw.toNat := by omega
      rw [show Flocq.bitsOfBinaryFloat mw ew (.finite s m e) =
        joinBits mw.toNat ew.toNat s 0 m by
          simp [Flocq.bitsOfBinaryFloat, joinBits, hm]]
      simp only [_root_.binaryFloatOfBitsAux,
        split_join mw.toNat ew.toNat s 0 m (by omega) (by omega)]
      simp only [ite_true, show (m : Int) ≠ 0 by omega, ite_false, Int.toNat_natCast]
      congr 1; omega

private theorem join_split (mw ew : Nat) (n : Int)
    (hn : 0 ≤ n ∧ n < (2 : Int) ^ (mw + ew + 1)) :
    let f := _root_.splitBits mw ew n
    joinBits mw ew f.1 f.2.1 f.2.2 = n := by
  have hp : 0 < (2 : Int) ^ mw := pow_pos (by decide) _
  have hq : 0 < (2 : Int) ^ ew := pow_pos (by decide) _
  have hpow : (2 : Int) ^ (mw + ew + 1) = 2 * (2 ^ mw * 2 ^ ew) := by
    rw [pow_succ, pow_add]; ring
  have hd := Int.ediv_mul_add_emod n ((2 : Int) ^ mw)
  have hr0 := Int.emod_nonneg n (ne_of_gt hp)
  have hr1 := Int.emod_lt_of_pos n hp
  have hnq0 : 0 ≤ n / (2 : Int) ^ mw := Int.ediv_nonneg hn.1 (le_of_lt hp)
  have hnq1 : n / (2 : Int) ^ mw < 2 * (2 : Int) ^ ew := by
    rw [Int.ediv_lt_iff_lt_mul hp]
    rw [hpow] at hn
    nlinarith [hn.2]
  unfold _root_.splitBits joinBits
  dsimp only
  rw [pow_add]
  by_cases hs : (2 : Int) ^ mw * 2 ^ ew ≤ n
  · have hlow : (2 : Int) ^ ew ≤ n / (2 : Int) ^ mw := by nlinarith
    have hmod : (n / (2 : Int) ^ mw) % (2 : Int) ^ ew =
        n / (2 : Int) ^ mw - 2 ^ ew := by
      rw [← Int.sub_emod_right (n / (2 : Int) ^ mw) ((2 : Int) ^ ew)]
      apply Int.emod_eq_of_lt <;> omega
    simp only [hs, decide_true, ite_true, hmod]
    nlinarith
  · have hlow : n / (2 : Int) ^ mw < (2 : Int) ^ ew := by nlinarith
    simp only [hs, decide_false, Bool.false_eq_true, ite_false,
      Int.emod_eq_of_lt hnq0 hlow, zero_add]
    exact hd

theorem bits_roundtrip : spec_bits_of_binary_float_of_bits canonical := by
  intro mw ew n h hn
  change Flocq.bitsOfBinaryFloat mw ew (_root_.binaryFloatOfBitsAux mw ew n) = n
  have hp : 0 < (2 : Int) ^ mw.toNat := pow_pos (by decide) _
  rw [encode_decode_fields mw ew n _ _ _ rfl
    ⟨Int.emod_nonneg _ (ne_of_gt hp), Int.emod_lt_of_pos _ hp⟩]
  apply join_split
  have hsum : (mw + ew + 1).toNat = mw.toNat + ew.toNat + 1 := by
    rcases h with ⟨hm, he, _⟩; omega
  simpa only [hsum] using hn

theorem float_roundtrip : spec_binary_float_of_bits_of_binary_float canonical := by
  intro mw ew x h hx
  exact decode_encode h x hx

theorem decoder_valid : spec_validBinary_def canonical :=
  ⟨fun _ _ _ => rfl, fun _ _ n h => decode_valid h n⟩

private theorem encoded_range {mw ew : Int} (h : validBitFormat mw ew)
    (x : BinaryFloat (mw + 1) ((2 : Int) ^ (ew - 1).toNat))
    (hx : _root_.validBinary _ _ x = true) :
    0 ≤ Flocq.bitsOfBinaryFloat mw ew x ∧
      Flocq.bitsOfBinaryFloat mw ew x < (2 : Int) ^ (mw + ew + 1).toNat := by
  have hp : 0 < (2 : Int) ^ mw.toNat := pow_pos (by decide) _
  have hwidth := exponent_width h
  have hprec := pow_next mw (by rcases h with ⟨hm, _, _⟩; omega)
  have hmax := h.2.2
  have hmw := h.1
  have hq : 1 < (2 : Int) ^ ew.toNat := by omega
  have hew : ew.toNat - 1 = (ew - 1).toNat := by omega
  have hsum : (mw + ew + 1).toNat = mw.toNat + ew.toNat + 1 := by
    rcases h with ⟨hm, he, _⟩; omega
  rw [hsum, pow_succ, pow_add]
  cases x <;> simp only [Flocq.bitsOfBinaryFloat, _root_.validBinary,
    decide_eq_true_eq, Int.add_sub_cancel, hprec, hew] at *
  all_goals split_ifs <;> simp_all only [pow_add] <;> constructor <;> nlinarith

theorem native_roundtrip : spec_B2Prim_Prim2B canonical := by
  intro laws x
  change Float.ofBits (Flocq.bitsOfBinaryFloat 52 11
    (_root_.binaryFloatOfBitsAux 52 11 (x.toBits.toNat : Int))).toNat.toUInt64 = x
  have hn : 0 ≤ (x.toBits.toNat : Int) ∧
      (x.toBits.toNat : Int) < 18446744073709551616 := by
    constructor
    · omega
    · change (x.toBits.toNat : Int) < 18446744073709551616
      exact_mod_cast x.toBits.toNat_lt
  have hr := bits_roundtrip 52 11 (x.toBits.toNat : Int) (by norm_num [validBitFormat, Int.toNat]) hn
  change Flocq.bitsOfBinaryFloat 52 11 (_root_.binaryFloatOfBitsAux 52 11
    (x.toBits.toNat : Int)) = (x.toBits.toNat : Int) at hr
  rw [hr]
  simpa using laws.ofBits_toBits x

theorem binary64_roundtrip : spec_Prim2B_B2Prim canonical := by
  intro laws x hx hnan
  change _root_.binaryFloatOfBitsAux 52 11
    ((Float.ofBits (Flocq.bitsOfBinaryFloat 52 11 x).toNat.toUInt64).toBits.toNat : Int) = x
  have hr := encoded_range (mw := 52) (ew := 11) (by norm_num [validBitFormat, Int.toNat]) x hx
  have hb : ((Flocq.bitsOfBinaryFloat 52 11 x).toNat.toUInt64.toNat : Int) =
      Flocq.bitsOfBinaryFloat 52 11 x := by
    have hlt : (Flocq.bitsOfBinaryFloat 52 11 x).toNat < 2 ^ 64 := by
      have hr1 := hr.2
      change Flocq.bitsOfBinaryFloat 52 11 x < 18446744073709551616 at hr1
      omega
    simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt,
      Int.toNat_of_nonneg hr.1]
  have hd := decode_encode (mw := 52) (ew := 11)
    (by norm_num [validBitFormat, Int.toNat]) x hx
  have hc : primitiveNanCanonical (_root_.binaryFloatOfBitsAux 52 11
      ((Flocq.bitsOfBinaryFloat 52 11 x).toNat.toUInt64.toNat : Int)) := by
    rw [hb, hd]
    exact hnan
  rw [laws.toBits_ofBits _ hc, hb]
  exact hd

/-- info: 'Flocq.ContractTests.bits_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bits_roundtrip
/-- info: 'Flocq.ContractTests.float_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms float_roundtrip
/-- info: 'Flocq.ContractTests.decoder_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decoder_valid
/-- info: 'Flocq.ContractTests.native_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms native_roundtrip
/-- info: 'Flocq.ContractTests.binary64_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms binary64_roundtrip

end Flocq.ContractTests
