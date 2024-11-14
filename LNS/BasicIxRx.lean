import LNS.Common
import LNS.Definitions

namespace LNS

lemma div_one_imp_le_one {Δ : ℝ} (hdn : ∃ n : ℕ, 1 = n * Δ) : Δ ≤ 1 := by
  cases le_or_lt Δ 0 with
  | inl h => linarith
  | inr h =>
    obtain ⟨n, hdn⟩ := hdn
    rw [hdn]
    apply (le_mul_iff_one_le_left h).mpr; norm_cast
    cases n
    · contrapose hdn; simp
    · simp only [le_add_iff_nonneg_left, zero_le]

lemma i_sub_r_eq_x (Δ x : ℝ) : Iₓ Δ x - Rₓ Δ x = x := by
  simp only [Iₓ, Rₓ, sub_sub_cancel]

lemma x_le_ix {Δ} (hd : 0 < Δ) x : x ≤ Iₓ Δ x :=
  (div_le_iff₀ hd).mp $ Int.le_ceil $ x / Δ

lemma ix_eq_n_delta {Δ : ℝ} (n : ℤ) (hd : Δ ≠ 0) : Iₓ Δ (n * Δ) = n * Δ := by
  unfold Iₓ
  rw [mul_div_cancel_right₀ _ hd]
  simp only [Int.ceil_intCast]

lemma ix_eq_neg_one {Δ : ℝ} (hd : Δ ≠ 0) (hdn : ∃ n : ℕ, 1 = n * Δ) : Iₓ Δ (-1) = -1 := by
  obtain ⟨n, hdn⟩ := hdn
  rw [hdn]
  have ⟨m, hm⟩ : ∃ m : ℤ, -(n * Δ) = m * Δ := by
    use -n; simp only [Int.cast_neg, Int.cast_natCast, neg_mul]
  rw [hm, ix_eq_n_delta _ hd]

lemma x_neg_iff_ix_neg {Δ} (hd : 0 < Δ) x : x ≤ 0 ↔ Iₓ Δ x ≤ 0 := by
  constructor
  · intro hx
    apply mul_nonpos_of_nonpos_of_nonneg _ (le_of_lt hd)
    rw [← Int.cast_zero, Int.cast_le, Int.ceil_le, Int.cast_zero]
    exact div_nonpos_of_nonpos_of_nonneg hx (le_of_lt hd)
  · exact le_trans (x_le_ix hd x)

lemma rx_eq_zero_iff {Δ x : ℝ} : Rₓ Δ x = 0 ↔ Iₓ Δ x = x := by
  simp only [Rₓ, Iₓ, sub_eq_zero]

lemma rx_eq_fract {Δ x : ℝ} (hd : Δ ≠ 0) (ix : Iₓ Δ x ≠ x) :
    Rₓ Δ x = Δ * (1 - Int.fract (x / Δ)) := by
  unfold Rₓ Iₓ at *
  rcases Int.fract_eq_zero_or_add_one_sub_ceil (x / Δ) with h | h
  · exfalso; apply ix
    simp only [Int.ceil_eq_self.mpr h]; field_simp
  · rw [h]; field_simp; ring

lemma rx_nonneg {Δ} (hd : 0 < Δ) x : 0 ≤ Rₓ Δ x :=
  Int.ceil_div_mul_sub_nonneg hd

lemma rx_lt_delta {Δ} (hd : 0 < Δ) x : Rₓ Δ x < Δ :=
  Int.ceil_div_mul_sub_lt hd

lemma ix_lt_zero (hd : 0 < Δ) (hx : x ≤ -Δ) : Iₓ Δ x < 0 := by
  unfold Iₓ
  apply mul_neg_of_neg_of_pos _ hd
  simp only [Int.cast_lt_zero]
  apply lt_of_le_of_lt _ (by norm_num : -1 < 0)
  simp only [Int.ceil_le, Int.reduceNeg, Int.cast_neg, Int.cast_one]
  rw [div_le_iff₀ hd, neg_mul, one_mul]
  exact hx

lemma ix_monotone (hd : 0 < Δ) : Monotone (Iₓ Δ) := by
  unfold Iₓ; intro a b hab; simp only
  rw [mul_le_mul_right hd, Int.cast_le]
  apply Int.ceil_le_ceil
  exact (div_le_div_right hd).mpr hab
