import LNS.Tactic
import LNS.Definitions
import LNS.Lemma61
import LNS.Lemma62
import LNS.Lemma63
import LNS.Lemma65

namespace LNS

noncomputable section

open Real

private def Qm_Range (Δ r : ℝ) := Qm_hi Δ r - Qm_lo Δ r

private def Qm_lo_YX (y x : ℝ) := U x / U y

private def Qm_hi_YX (y x : ℝ) := Vm x / Vm y

private def Qm_Range_YX (y x : ℝ) := Qm_hi_YX y x - Qm_lo_YX y x

private def Max_Xm (y : ℝ) := Bm y / Am y

private def dQm_Range_YX (y x : ℝ) := (x - 1) / (y * x * x * (2 * x - 1) * U y * Vm y) * (-Am y * x + Bm y)

lemma Vm_pos (hx : 1 < x) : 0 < Vm x := by
  have i1 : ∀ x ∈ Set.Ici (1:ℝ) , 2*x - 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have i2 : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have eq : Vm 1 = 0 := by unfold Vm; norm_num
  rw [← eq]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) _ _ Set.left_mem_Ici (le_of_lt hx) hx
  · unfold Vm; fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; unfold Vm
  get_deriv (fun {X} ↦ 2 * log X - log (2 * X - 1)) at x
  simp
  constructor <;> linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]
  have : 2*x - 1 > 0 := by linarith
  field_simp; linarith

lemma deriv_Cm (hy : 1 < y) : deriv Cm y = 2 * (y - 1) / (y ^ 2 * (2 * y - 1)) := by
  unfold Cm
  get_deriv (fun Y ↦ 2 * log Y - 2 * log (2 * Y - 1) + 2 - 2 / Y) at y
  simp
  split_ands <;> linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]
  have : 2 * y - 1 > 0 := by linarith
  field_simp; ring_nf

lemma Cm_pos (hy : 1 < y) : 0 < Cm y := by
  have eq : Cm 1 = 0 := by unfold Cm; norm_num
  rw [← eq]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) _ _ Set.left_mem_Ici (le_of_lt hy) hy
  · unfold Cm
    have : ∀ x ∈ Set.Ici (1:ℝ) , 2*x - 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; rw [deriv_Cm hx]
  have : 2*x - 1 > 0 := by linarith
  have : x - 1 > 0 := by linarith
  positivity

lemma Am_pos (hy : 1 < y) : 0 < Am y := by
  have e : Am y = (Cm y) * y := by simp only [Am, Cm]; field_simp; ring_nf
  rw [e]; apply mul_pos (Cm_pos hy) (by linarith)

lemma Bm_pos (hy : 1 < y) : 0 < Bm y := by
  unfold Bm; apply mul_pos (by linarith) (Vm_pos hy)

private def Rm (y : ℝ) := Am y - (Bm y) / y

private def dRm (y : ℝ) := 2 * log y - 2 * log (2 * y - 1) + 2 - 2 / y

private lemma deriv_Rm (hy : 1 < y) : deriv Rm y = dRm y := by
  unfold Rm Am Bm dRm Vm
  get_deriv (fun Y ↦ 2 * Y * log Y - 2 * Y * log (2 * Y - 1) + 2 * Y - 2 - Y * (2 * log Y - log (2 * Y - 1)) / Y) at y
  simp
  split_ands <;> linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]
  have : 2 * y - 1 > 0 := by linarith
  field_simp; ring_nf

private lemma deriv_dRm (hy : 1 < y) : deriv dRm y = 2 * (y - 1) / (y ^ 2 * (2 * y - 1)) := by
  unfold dRm
  get_deriv (fun Y ↦ 2 * log Y - 2 * log (2 * Y - 1) + 2 - 2 / Y) at y
  simp
  split_ands <;> linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]
  have : 2 * y - 1 > 0 := by linarith
  field_simp; ring_nf

private lemma dRm_pos (hy : 1 < y) : 0 < dRm y := by
  have eq : dRm 1 = 0 := by unfold dRm; norm_num
  rw [← eq]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) _ _ Set.left_mem_Ici (le_of_lt hy) hy
  · unfold dRm
    have : ∀ x ∈ Set.Ici (1:ℝ) , 2*x - 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; rw [deriv_dRm hx]
  have : 2*x - 1 > 0 := by linarith
  have : x - 1 > 0 := by linarith
  positivity

private lemma Rm_pos (hy : 1 < y) : 0 < Rm y := by
  have eq : Rm 1 = 0 := by unfold Rm Am Bm Vm; norm_num
  rw [← eq]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) _ _ Set.left_mem_Ici (le_of_lt hy) hy
  · unfold Rm Am Bm Vm
    have : ∀ x ∈ Set.Ici (1:ℝ) , 2*x - 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; rw [deriv_Rm hx]; exact dRm_pos hx

private lemma Max_Xm_lt_X (h : 1 < y) : Max_Xm y < y := by
  unfold Max_Xm
  have i1 : Am y > 0 := Am_pos h
  have i2 : y / Am y > 0 := by positivity
  have i3 : Am y - (Bm y) / y > 0 := Rm_pos h
  simp only [gt_iff_lt, sub_pos] at i3
  have i3 : (Bm y / y) * (y / Am y) < Am y * (y / Am y) := (mul_lt_mul_right i2).mpr i3
  field_simp at i3
  exact i3

private def Mm (y : ℝ) := (Bm y - Am y) / y

private lemma deriv_Mm (hy : 1 < y) : deriv Mm y = 2 * (y - 1) ^ 2 / (y ^ 2 * (2 * y - 1)) := by
  unfold Mm Am Bm Vm
  get_deriv (fun Y ↦ (Y * (2 * log Y - log (2 * Y - 1)) - (2 * Y * log Y - 2 * Y * log (2 * Y - 1) + 2 * Y - 2)) / Y) at y
  simp
  split_ands <;> linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]
  have : 2 * y - 1 > 0 := by linarith
  field_simp; ring_nf

private lemma Mm_pos (hy : 1 < y) : 0 < Mm y := by
  have eq : Mm 1 = 0 := by unfold Mm Am Bm Vm; norm_num
  rw [← eq]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) _ _ Set.left_mem_Ici (le_of_lt hy) hy
  · unfold Mm Am Bm Vm
    have : ∀ x ∈ Set.Ici (1:ℝ) , 2*x - 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; rw [deriv_Mm hx]
  have : x - 1 > 0 := by linarith
  have : 2*x - 1 > 0 := by linarith
  positivity

private lemma Max_Xm_gt_one (h : 1 < y) : 1 < Max_Xm y := by
  unfold Max_Xm
  have i1 : Am y > 0 := Am_pos h
  have i2 : (Bm y - Am y) / y > 0 := Mm_pos h
  field_simp at i2
  exact (one_lt_div i1).mpr i2

private lemma deriv_Qm_Range_YX (hy: 1 < y) : Set.EqOn (deriv (Qm_Range_YX y)) (dQm_Range_YX y) (Set.Ioi 1) := by
  have i1 := Vm_pos hy
  have i4 := U_pos hy
  intro X hX; simp only [Set.mem_Ioi] at hX; unfold Qm_Range_YX Qm_hi_YX Qm_lo_YX U Vm
  get_deriv (fun X ↦ (2 * log X - log (2 * X - 1)) / (2 * log y - log (2 * y - 1)) - (1 / X + log X - 1) / (1 / y + log y - 1)) at X
  simp
  rw [(by simp only [one_div]: y⁻¹  = 1 / y)]
  split_ands <;> try linarith
  unfold Vm at i1; linarith
  unfold U at i4; linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]
  simp
  simp only [← one_div]
  rw [(by simp only [Vm] : 2 * log y - log (2 * y - 1) = Vm y), (by simp only [U] : 1 / y + log y - 1 = U y)]
  have : 2*X - 1 > 0 := by linarith
  have e1 : (2 * (1 / X) - 2 / (2 * X - 1)) * Vm y / Vm y ^ 2 - (-1 / X ^ 2 + 1 / X) * U y / U y ^ 2
      = (X-1)*(2*U y * X  - Vm y*(2*X -1))/(U y * Vm y * X^2 * (2*X-1)) := by field_simp; ring_nf
  have e2 : dQm_Range_YX y X = (X-1)*((-Am y * X + Bm y)/y)/ (U y * Vm y*X^2*(2*X-1)) := by
    unfold dQm_Range_YX; field_simp; ring_nf; simp only [true_or]
  have e3 : (-Am y * X + Bm y) / y = (2 * U y * X  - Vm y * (2 * X - 1)) := by
    unfold Am Bm Vm U ; field_simp; ring
  rw [e1, e2, e3]

private lemma max_Qm_Range_YX (h1: 1 ≤ x) (h2 : x ≤ y) : Qm_Range_YX y x ≤ Qm_Range_YX y (Max_Xm y) := by
  by_cases hxy : x = 1 ∧ y = 1
  · rw [hxy.1, hxy.2]
    unfold Qm_Range_YX Qm_hi_YX Qm_lo_YX U Vm; norm_num
  have : ∀ x ∈ Set.Ici (1:ℝ) , 2*x - 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have hY : y > 1 := by
    by_cases h : y ≠ 1
    · exact lt_of_le_of_ne (le_trans h1 h2) h.symm
    · contrapose hxy
      simp only [not_and, Classical.not_imp, Decidable.not_not]; simp at h
      exact ⟨by linarith, h⟩
  have iA : Am y > 0 := Am_pos hY
  have iV := Vm_pos hY
  have iU := U_pos hY
  have cont : ContinuousOn (Qm_Range_YX y) (Set.Ici 1) := by
    unfold Qm_Range_YX Qm_hi_YX Qm_lo_YX U Vm
    fun_prop (disch := assumption)
  have first_half : StrictMonoOn (Qm_Range_YX y) (Set.Icc 1 (Max_Xm y)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 1 (Max_Xm y))
    apply ContinuousOn.mono cont
    rw [Set.Icc_subset_Ici_iff]
    linarith [Max_Xm_gt_one hY]
    intro x hx; simp only [interior_Icc, Set.mem_Ioo] at hx
    rw [deriv_Qm_Range_YX hY, dQm_Range_YX ]
    have i1 : Am y * x < Am y * Max_Xm y := (mul_lt_mul_left iA).mpr hx.right
    unfold Max_Xm at i1; field_simp at i1
    have : -Am y * x + Bm y > 0 := by linarith
    have : (x - 1) > 0 := by linarith
    have : 2*x - 1 > 0 := by linarith
    have : x > 0 := by linarith
    positivity
    simp only [Set.mem_Ioi]; linarith
  have second_half : StrictAntiOn (Qm_Range_YX y) (Set.Icc (Max_Xm y) y) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc (Max_Xm y) y)
    apply ContinuousOn.mono cont
    rw [Set.Icc_subset_Ici_iff]
    linarith [Max_Xm_gt_one hY]; linarith [Max_Xm_lt_X hY]
    intro x hx; simp only [interior_Icc, Set.mem_Ioo] at hx
    rw [deriv_Qm_Range_YX hY, dQm_Range_YX ]
    have i1 : Am y * x > Am y * Max_Xm y := (mul_lt_mul_left iA).mpr hx.left
    unfold Max_Xm at i1; field_simp at i1
    have : (x - 1) > 0 := by linarith [Max_Xm_gt_one hY]
    have : x > 0 := by linarith
    apply mul_neg_of_pos_of_neg
    have : 2*x - 1 > 0 := by linarith
    positivity; linarith
    simp only [Set.mem_Ioi]; linarith[Max_Xm_gt_one hY]
  by_cases x ≤ (Max_Xm y)
  apply StrictMonoOn.monotoneOn first_half
  simp only [Set.mem_Icc] ; constructor <;> linarith
  simp only [Set.mem_Icc] ; constructor <;> linarith
  assumption
  apply StrictAntiOn.antitoneOn second_half
  simp only [Set.mem_Icc] ; constructor <;> linarith
  simp only [Set.mem_Icc] ; constructor <;> linarith
  linarith

private lemma Qm_Range_YX_eq_Qm_range (hΔ : 0 < Δ) (hr: 0 ≤ r) : Qm_Range Δ r = Qm_Range_YX (2^Δ) (2^r) := by
  unfold Qm_Range Qm_Range_YX
  have hΔ0 : Δ > 0 := by linarith
  have e1 : ∀ x ≥ (0:ℝ), (2:ℝ)^(-x) = 1/2^x := by intro x _; rw [rpow_neg]; ring_nf; simp only [Nat.ofNat_nonneg]
  have e2 : ∀ x ≥ (0:ℝ), log ((2:ℝ)^x) = x * log 2 := by intro x _; rw [log_rpow]; simp only [Nat.ofNat_pos]
  have eh : Qm_lo Δ r = Qm_lo_YX (2 ^ Δ) (2 ^ r) := by
    unfold Qm_lo Qm_lo_YX U
    simp only [e1 r hr, e1 Δ (le_of_lt hΔ0), e2 r hr, e2 Δ (le_of_lt hΔ0)]
  have el : Qm_hi Δ r = Qm_hi_YX (2 ^ Δ) (2 ^ r) := by
    unfold Qm_hi Qm_hi_YX Vm
    rw [Qm_of_Fm (by simp only [Set.mem_Iio, Left.neg_neg_iff,zero_lt_one]) hr hΔ]
    have : Fm (2 ^ Δ) (2 ^ (-1:ℝ )) > 0 := by
      apply Fm_pos
      simp only [Set.mem_Ioo, Nat.ofNat_pos,rpow_pos_of_pos, true_and]
      ring_nf; field_simp; apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hΔ
    have : 2 * log (2 ^ Δ) - log (2 * 2 ^ Δ - 1) > 0 := by apply Vm_pos (one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hΔ)
    simp only [Function.comp_apply]; field_simp
    have e1 : ∀ r ≥ (0:ℝ),  log (2 ^ r - 2 ^ (-1:ℝ )) = log (2*2^r -1) - log 2 := by
      intro r hr
      have : (2:ℝ) ^ r - 2 ^ (-1:ℝ ) = (2*2^r -1)/2 := by field_simp; ring_nf
      rw [this, log_div]
      have : (2:ℝ)^r ≥ 1 := by apply one_le_rpow (by simp only [Nat.one_le_ofNat]) hr
      linarith; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    have e2 : log (1 / 2) = - log 2 := by simp only [one_div, log_inv]
    simp only [Function.comp_apply, Fm, (by field_simp; ring: ((1:ℝ) - 2 ^ (-1:ℝ)) = 1/2), e1 r hr, e1 Δ (le_of_lt hΔ), e2]
    field_simp; ring_nf
  rw [el, eh]

lemma lemma66sub (hΔ : r < Δ) (hr : 0 ≤ r) : Qm_Range Δ r ≤ Qm_Range Δ (Rm_opt Δ) := by
  have hΔ0 : 0 < Δ := by linarith
  have i1 : (2:ℝ) ^ Δ > 1 := by apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hΔ0
  have i2 : (2:ℝ) ^ r ≥ 1 := by apply one_le_rpow (by simp only [Nat.one_le_ofNat]) hr
  have hRm_opt0 : 0 < Rm_opt Δ := logb_pos (by simp only [Nat.one_lt_ofNat]) (Max_Xm_gt_one i1)
  rw [Qm_Range_YX_eq_Qm_range hΔ0 hr, Qm_Range_YX_eq_Qm_range hΔ0 (le_of_lt hRm_opt0)]
  have : 2 ^ Rm_opt Δ = Max_Xm (2 ^ Δ) := by
    have iA := @Am_pos (2 ^ Δ) i1
    have iB := @Bm_pos (2 ^ Δ) i1
    unfold Rm_opt Max_Xm; simp only
    rw [Real.rpow_logb, Am, Bm, Vm]; simp only [Nat.ofNat_pos]
    simp only [ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
    positivity
  rw [this]
  apply max_Qm_Range_YX i2
  apply rpow_le_rpow_of_exponent_le (by simp only [Nat.one_le_ofNat]) (le_of_lt hΔ)

lemma qm_upper_bound (hi : i ≤ -1) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    Qm Δ i r ≤ Qm_hi Δ r := by
  apply Lemma65 hr1 hr2 _ (by norm_num) hi
  simp only [Set.mem_Iio]; linarith

lemma qm_lower_bound (hi₀ : i₀ < 0) (hi : i ≤ i₀) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    Qm_lo Δ r ≤ Qm Δ i r := by
  apply le_of_tendsto (Lemma61m (by linarith) hr1)
  simp only [Filter.eventually_atBot]
  use i; intro b hb
  apply Lemma65 hr1 hr2 _ _ hb
  simp only [Set.mem_Iio]; linarith
  simp only [Set.mem_Iio]; linarith

lemma Lemma66 (hi : i ≤ -1) (hc : c ≤ -1) (hr : 0 ≤ r) (hΔ : r < Δ) :
    |Qm Δ i r - Qm Δ c r| ≤ Qm_hi Δ (Rm_opt Δ) - Qm_lo Δ (Rm_opt Δ) := by
  have i1 : Qm_hi Δ r - Qm_lo Δ r ≤ Qm_hi Δ (Rm_opt Δ) - Qm_lo Δ (Rm_opt Δ) := by apply lemma66sub hΔ hr
  have case1 : Qm Δ i r - Qm Δ c r ≥ 0 → |Qm Δ i r - Qm Δ c r| ≤ Qm_hi Δ (Rm_opt Δ) - Qm_lo Δ (Rm_opt Δ) := by
    intro i0
    have i2 : Qm Δ i r ≤ Qm_hi Δ r := by apply qm_upper_bound hi hr hΔ
    have i3 : Qm_lo Δ r ≤ Qm Δ c r := by apply qm_lower_bound (by norm_num) hc hr hΔ
    have e0 : |Qm Δ i r - Qm Δ c r| = Qm Δ i r - Qm Δ c r := by apply abs_of_nonneg; linarith
    linarith
  apply by_cases case1; simp
  intro i0
  have i2 : Qm Δ c r ≤ Qm_hi Δ r := by apply qm_upper_bound hc hr hΔ
  have i3 : Qm_lo Δ r ≤ Qm Δ i r := by apply qm_lower_bound (by norm_num) hi hr hΔ
  have e0 : |Qm Δ i r - Qm Δ c r| = -(Qm Δ i r - Qm Δ c r) := by apply abs_of_neg; linarith
  linarith
