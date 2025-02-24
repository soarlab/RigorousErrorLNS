import LNS.Tactic
import LNS.Definitions
import LNS.Lemma61
import LNS.Lemma62

namespace LNS

noncomputable section

open Real

private def Qp_Range (Δ r : ℝ) := Qp_hi Δ r  - Qp_lo Δ r

private def Qp_hi_YX (y x : ℝ) := U x / U y

private def Qp_lo_YX (y x : ℝ) := V x / V y

private def Qp_Range_YX (y x : ℝ) := Qp_hi_YX y x - Qp_lo_YX y x

private def Max_X (y : ℝ) := B y / A y

private def dQp_Range_YX (y x : ℝ) := (y * (x - 1))/ (x * x * (x + 1) * (B y + A y)* B y) * (-A y * x + B y)

lemma V_pos (hx : 1 < x) : 0 < V x := by
  have eq : V 1 = 0 := by unfold V; norm_num
  rw [← eq]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) _ _ Set.left_mem_Ici (le_of_lt hx) hx
  · unfold V
    have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    fun_prop (disch := assumption)
  unfold V; simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx
  get_deriv (fun {X} ↦ 2 * log (X + 1) - log X - 2 * log 2) at x
  simp
  constructor <;> linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]
  field_simp; linarith

lemma deriv_C (hy : 1 < y) : deriv C y = 2 / (y * (y + 1) ^ 2) := by
  unfold C
  get_deriv (fun {Y} ↦ -2 * Y / (Y + 1) + 2 * log Y - 2 * log (Y + 1) + 2 * log 2 + 1) at y
  simp
  split_ands <;> linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]
  field_simp; ring_nf

lemma C_pos (hy : 1 < y) : 0 < C y := by
  have eq : C 1 = 0 := by unfold C; norm_num
  rw [← eq]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) _ _ Set.left_mem_Ici (le_of_lt hy) hy
  · unfold C
    have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; rw [deriv_C hx]; positivity

lemma deriv_A (hy : 1 < y) : deriv A y = C y := by
  unfold A C
  get_deriv (fun {Y} ↦ -2 * Y * (log (Y + 1) - log Y - log 2) - Y + 1) at y
  simp
  constructor <;> linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]
  field_simp; ring_nf

lemma A_pos (hy : 1 < y) : 0 < A y := by
  have eq : A 1 = 0 := by unfold A; norm_num
  rw [← eq]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) _ _ Set.left_mem_Ici (le_of_lt hy) hy
  · unfold A
    have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; rw [deriv_A hx]; exact C_pos hx

lemma B_pos (hy : 1 < y) : 0 < B y := by
  have : B y = y * V y := by unfold B V; ring_nf
  rw [this]; apply mul_pos (by linarith) (V_pos hy)

private def R (y:ℝ) := A y - (B y) / y

private def dR (y:ℝ) := 2 * log y - 2 * log (y + 1) - 1 + 2 * log 2 + 1 / y

private lemma deriv_R (hy : 1 < y) : deriv R y = dR y := by
  unfold R A B dR
  get_deriv (fun Y ↦ -2 * Y * (log (Y + 1) - log Y - log 2) - Y + 1 - Y * (2 * log (Y + 1) - log Y - 2 * log 2) / Y) at y
  simp
  split_ands <;> linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]; field_simp; ring_nf

private lemma deriv_dR (hy : 1 < y) : deriv dR y = (y - 1) / (y ^ 2 * (y + 1)) := by
  unfold dR
  get_deriv (fun Y ↦ 2 * log Y - 2 * log (Y + 1) - 1 + 2 * log 2 + 1 / Y) at y
  simp
  split_ands <;> linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]; field_simp; ring_nf

private lemma dR_pos (hy : 1 < y) : 0 < dR y := by
  have eq : dR 1 = 0 := by unfold dR; norm_num; ring
  rw [← eq]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) _ _ Set.left_mem_Ici (le_of_lt hy) hy
  · unfold dR
    have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; rw [deriv_dR hx]
  have : x - 1 > 0 := by linarith
  positivity

private lemma R_pos (hy : 1 < y) : 0 < R y := by
  have eq : R 1 = 0 := by unfold R A B; norm_num
  rw [← eq]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) _ _ Set.left_mem_Ici (le_of_lt hy) hy
  · unfold R A B
    have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; rw [deriv_R hx]; exact dR_pos hx

private lemma Max_X_lt_X (hy : 1 < y) : Max_X y < y := by
  unfold Max_X
  have i1 : A y > 0 := A_pos hy
  have i2 : y / A y > 0 := by positivity
  have i3 : A y - (B y) / y > 0 := R_pos hy
  simp only [gt_iff_lt, sub_pos] at i3
  have i3 : (B y / y) * (y / A y) < A y * (y / A y) := (mul_lt_mul_right i2).mpr i3
  field_simp at i3
  exact i3

def M (y:ℝ) := (B y - A y) / y

private lemma deriv_M (hy : 1 < y) : deriv M y = (y - 1) ^ 2 / (y ^ 2 * (y + 1)) := by
  unfold M A B
  get_deriv (fun {Y} ↦ (Y * (2 * log (Y + 1) - log Y - 2 * log 2) - (-2 * Y * (log (Y + 1) - log Y - log 2) - Y + 1)) / Y) at y
  simp
  split_ands <;> linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]; field_simp; ring_nf

private lemma M_pos (hy : 1 < y) : 0 < M y := by
  have eq : M 1 = 0 := by unfold M A B; norm_num
  rw [← eq]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) _ _ Set.left_mem_Ici (le_of_lt hy) hy
  · unfold M A B
    have : ∀ x ∈ Set.Ici (1:ℝ) , x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; rw [deriv_M hx]
  have : x - 1 > 0 := by linarith
  positivity

private lemma Max_X_gt_one (hy : 1 < y) : 1 < Max_X y := by
  unfold Max_X
  have i1 : A y > 0 := A_pos hy
  have i2 : (B y - A y) / y > 0 := M_pos hy
  field_simp at i2
  exact (one_lt_div i1).mpr i2

private lemma deriv_Qp_Range_YX (hy: 1 < y) : Set.EqOn (deriv (Qp_Range_YX y)) (dQp_Range_YX y) (Set.Ioi 0) := by
  have i1 : (2 * log (y + 1) - log y - 2 * log 2) > 0 := V_pos hy
  have i2 : A y > 0 := A_pos hy
  have i3 : B y > 0 := B_pos hy
  have i4 : 1 / y + log y - 1 > 0 := U_pos hy
  intro X hX; unfold Qp_Range_YX Qp_hi_YX Qp_lo_YX U V
  get_deriv (fun X ↦ (1 / X + log X - 1) / (1 / y + log y - 1) -
        (2 * log (X + 1) - log X - 2 * log 2) / (2 * log (y + 1) - log y - 2 * log 2)) within (Set.Ioi 0)
  simp
  intro x hx; rw [(by simp only [one_div] : y⁻¹ = 1 / y)]
  split_ands <;> try linarith
  simp only [toFun] at h
  rw [h.right X hX]; simp
  simp only [Set.mem_Ioi] at hX
  simp only [← one_div]
  have : X ^ 2 * X * y * (1 + log y * y - y) ^ 2 >0 := by
    have : X ^ 2 * X * y * (1 + log y * y - y) ^ 2 = X ^ 2 * X * y ^ 3 * (1 / y + log y - 1) ^ 2 := by field_simp; ring
    rw [this]; positivity
  unfold dQp_Range_YX
  field_simp
  unfold A B; ring

private lemma max_Qp_Range_YX (h1: 1 ≤ x) (h2 : x < y): Qp_Range_YX y x ≤ Qp_Range_YX y (Max_X y) := by
  have : ∀ x ∈ Set.Ici (1:ℝ), x + 1 ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ), x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
  have hy : y > 1 := by linarith
  have iA : A y > 0 := A_pos hy
  have iB : B y > 0 := B_pos hy
  have cont : ContinuousOn (Qp_Range_YX y) (Set.Ici 1) := by
    unfold Qp_Range_YX Qp_hi_YX Qp_lo_YX U V
    fun_prop (disch := assumption)
  have first_half : StrictMonoOn (Qp_Range_YX y) (Set.Icc 1 (Max_X y)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 1 (Max_X y))
    apply ContinuousOn.mono cont
    rw [Set.Icc_subset_Ici_iff]
    linarith [Max_X_gt_one hy]
    intro x hx; simp only [interior_Icc, Set.mem_Ioo] at hx
    rw [deriv_Qp_Range_YX hy, dQp_Range_YX ]
    have i1 : A y * x < A y * Max_X y := (mul_lt_mul_left iA).mpr hx.right
    unfold Max_X at i1; field_simp at i1
    have : -A y * x + B y > 0 := by linarith
    have : (x - 1) > 0 := by linarith
    have : x > 0 := by linarith
    positivity
    simp only [Set.mem_Ioi]; linarith
  have second_half : StrictAntiOn (Qp_Range_YX y) (Set.Icc (Max_X y) y) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc (Max_X y) y)
    apply ContinuousOn.mono cont
    rw [Set.Icc_subset_Ici_iff]
    linarith [Max_X_gt_one hy]; linarith [Max_X_lt_X hy]
    intro x hx; simp only [interior_Icc, Set.mem_Ioo] at hx
    rw [deriv_Qp_Range_YX hy, dQp_Range_YX ]
    have i1 : A y * x > A y * Max_X y := (mul_lt_mul_left iA).mpr hx.left
    unfold Max_X at i1; field_simp at i1
    have : (x - 1) > 0 := by linarith [Max_X_gt_one hy]
    have : x > 0 := by linarith
    apply mul_neg_of_pos_of_neg
    positivity; linarith
    simp only [Set.mem_Ioi]; linarith[Max_X_gt_one hy]
  by_cases (x ≤ (Max_X y))
  apply StrictMonoOn.monotoneOn first_half
  simp only [Set.mem_Icc]; constructor <;> linarith
  simp only [Set.mem_Icc]; constructor <;> linarith
  assumption
  apply StrictAntiOn.antitoneOn second_half
  simp only [Set.mem_Icc]; constructor <;> linarith
  simp only [Set.mem_Icc]; constructor <;> linarith
  linarith

private lemma Qp_Range_YX_eq_Qp_range (hΔ : 0 < Δ) (hr: 0 ≤ r) : Qp_Range Δ r =  Qp_Range_YX (2^Δ) (2^r) := by
  unfold Qp_Range Qp_Range_YX
  have hΔ0 : Δ > 0 := by linarith
  have e1 : ∀ x ≥ (0:ℝ), (2:ℝ)^(-x) = 1/2^x := by intro x _; rw [rpow_neg]; ring_nf; simp only [Nat.ofNat_nonneg]
  have e2 : ∀ x ≥ (0:ℝ), log ((2:ℝ)^x) = x * log 2 := by intro x _; rw [log_rpow]; simp only [Nat.ofNat_pos]
  have eh : Qp_hi Δ r = Qp_hi_YX (2 ^ Δ) (2 ^ r) := by
    unfold Qp_hi Qp_hi_YX U
    simp only [e1 r hr, e1 Δ (le_of_lt hΔ0), e2 r hr, e2 Δ (le_of_lt hΔ0)]
  have el : Qp_lo Δ r = Qp_lo_YX (2 ^ Δ) (2 ^ r) := by
    unfold Qp_lo Qp_lo_YX V
    simp only [Qp_of_Fp hΔ, Fp, neg_add_rev, Function.comp_apply, rpow_zero,
      (by linarith : (-1 : ℝ) + -1 = -2), (by linarith : (1 : ℝ) + 1 = 2), neg_mul]
    have e1 : (-(2 * log 2) + 2 * log (1 + 2 ^ r) - log (2 ^ r)) = (2 * log (2 ^ r + 1) - log (2 ^ r) - 2 * log 2) := by ring_nf
    have e2 : (-(2 * log 2) + 2 * log (1 + 2 ^ Δ) - log (2 ^ Δ)) = (2 * log (2 ^ Δ + 1) - log (2 ^ Δ) - 2 * log 2) := by ring_nf
    rw [e1, e2]
  rw [el, eh]

private lemma lemma63sub (hΔ : r < Δ) (hr : 0 ≤ r) : Qp_Range Δ r ≤ Qp_Range Δ (Rp_opt Δ) := by
  have hΔ0 : 0 < Δ := by linarith
  have i1 : (2:ℝ) ^ Δ > 1 := by apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hΔ0
  have i2 : (2:ℝ) ^ r ≥ 1 := by apply one_le_rpow (by simp only [Nat.one_le_ofNat]) hr
  have hRp_opt0 : 0 < Rp_opt Δ := logb_pos (by simp only [Nat.one_lt_ofNat]) (Max_X_gt_one i1)
  rw [Qp_Range_YX_eq_Qp_range hΔ0 hr, Qp_Range_YX_eq_Qp_range hΔ0 (le_of_lt hRp_opt0)]
  have : 2 ^ Rp_opt Δ = Max_X (2 ^ Δ) := by
    have iA := @A_pos (2 ^ Δ) i1
    have iB := @B_pos (2 ^ Δ) i1
    unfold Rp_opt Max_X; simp only
    rw [Real.rpow_logb, B, A]; simp only [Nat.ofNat_pos]
    simp only [ne_eq, OfNat.ofNat_ne_one, not_false_eq_true]
    positivity
  rw [this]
  apply max_Qp_Range_YX i2
  apply rpow_lt_rpow_of_exponent_lt (by simp only [Nat.one_lt_ofNat]) hΔ

lemma q_lower_bound (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) : Qp_lo Δ r ≤ Qp Δ i r :=
  Lemma62 hr1 hr2 hi Set.right_mem_Iic hi

lemma q_upper_bound (hi : i ≤ 0) (hr : 0 ≤ r) (hΔ : r < Δ) : Qp Δ i r ≤ Qp_hi Δ r := by
  apply ge_of_tendsto (Lemma61 (by linarith) hr)
  simp only [Filter.eventually_atBot]
  use i; intro b hb
  apply Lemma62 hr hΔ (by simp only [Set.mem_Iic]; linarith) (by simp only [Set.mem_Iic]; linarith) hb

lemma Lemma63 (hi : i ≤ 0) (hc : c ≤ 0) (hr : 0 ≤ r) (hΔ : r < Δ) :
    |Qp Δ i r - Qp Δ c r| ≤ Qp_hi Δ (Rp_opt Δ) - Qp_lo Δ (Rp_opt Δ) := by
  have i1 : Qp_hi Δ r - Qp_lo Δ r ≤ Qp_hi Δ (Rp_opt Δ) - Qp_lo Δ (Rp_opt Δ) := by apply lemma63sub hΔ hr
  have case1 : Qp Δ i r - Qp Δ c r ≥ 0 → |Qp Δ i r - Qp Δ c r| ≤ Qp_hi Δ (Rp_opt Δ) - Qp_lo Δ (Rp_opt Δ) := by
    intro i0
    have i2 : Qp Δ i r ≤ Qp_hi Δ r := by apply q_upper_bound; linarith; assumption; assumption
    have i3 : Qp_lo Δ r ≤ Qp Δ c r := by apply q_lower_bound; assumption; assumption; assumption
    have e0 : |Qp Δ i r - Qp Δ c r| = Qp Δ i r - Qp Δ c r := by apply abs_of_nonneg; linarith
    linarith
  apply by_cases case1; simp
  intro i0
  have i2 : Qp Δ c r ≤ Qp_hi Δ r := by apply q_upper_bound; linarith; assumption; assumption
  have i3 : Qp_lo Δ r ≤ Qp Δ i r := by apply q_lower_bound; assumption; assumption; assumption
  have e0 : |Qp Δ i r - Qp Δ c r| = -(Qp Δ i r - Qp Δ c r) := by apply abs_of_neg; linarith
  linarith
