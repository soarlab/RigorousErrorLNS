import LNS.Common
import LNS.Tactic
import LNS.Definitions
import LNS.BasicPhi

namespace LNS

noncomputable section

open Real

private lemma one_minus_two_pow_ne_zero3 (hi : i < (0:ℝ)) (hr : r > 0) :
    1 - (2:ℝ) ^ (i - r) ≠ 0 := by
  apply one_minus_two_pow_ne_zero2; linarith

private lemma one_minus_two_pow_ne_zero4 (hi : i < (0:ℝ)) (hr : r ≥ 0) :
    1 - (2:ℝ) ^ (i - r) ≠ 0 := by
  apply one_minus_two_pow_ne_zero2; linarith

private lemma aux_inq1 (hi : i ∈ (Set.Iio (0:ℝ))) :
    ∀ x ∈ Set.Ioi 0, ¬1 - (2:ℝ) ^ (i - x) = 0 ∧ ¬1 - (2:ℝ) ^ i = 0 := by
  simp_all only [Set.mem_Iio, Set.mem_Ioi, one_minus_two_pow_ne_zero2, not_false_eq_true, and_true]
  intro x hx
  exact one_minus_two_pow_ne_zero3 hi hx

private lemma aux_inq1' (hi : i ∈  (Set.Iio (0:ℝ))) :
    ∀ x ∈ Set.Ici 0, ¬1 - (2:ℝ) ^ (i - x) = 0 ∧ ¬1 - (2:ℝ) ^ i = 0 := by
  simp_all only [Set.mem_Iio, Set.mem_Ici, one_minus_two_pow_ne_zero2, not_false_eq_true, and_true]
  intro x hx
  have: (2:ℝ) ^ (i - x) < 1 := by apply rpow_lt_one_of_one_lt_of_neg; simp only [Nat.one_lt_ofNat]; linarith
  linarith

private lemma aux_inq2 (hi : i ∈  (Set.Iio (0:ℝ))) :
    ∀ x ∈ Set.Ici 0, ¬1 - (2:ℝ) ^ (i - x) = 0 :=by
  simp_all only [Set.mem_Iio, Set.mem_Ioi, one_minus_two_pow_ne_zero2, not_false_eq_true, and_true]
  intro x hx; simp only [Set.mem_Ici] at hx
  apply one_minus_two_pow_ne_zero2; linarith

private lemma aux_eq1 : rexp (-(log 2 * r)) = 1/ 2 ^ r := by
  rw [exp_neg, exp_mul, exp_log]; field_simp; simp only [Nat.ofNat_pos]

private lemma aux_eq2 : (2:ℝ) ^ ((x:ℝ) - r) = 2^x / 2^r := by
  simp only [Nat.ofNat_pos, rpow_sub];

/-
  Basic properties of Ep and Em
-/

lemma Ep_eq_zero (i : ℝ) : Ep i 0 = 0 := by simp only [Ep, sub_zero, sub_self, zero_mul, add_zero]

lemma Em_eq_zero (i : ℝ) : Em i 0 = 0 := by simp only [Em, sub_zero, neg_add_cancel, zero_mul, sub_self]

/-
  Continuity and differentiability of Ep(i, r) and Em(i, r) with respect to r
-/

lemma deriv_Ep_r : deriv (Ep i) = fun (r : ℝ) => ((2:ℝ)^i - (2:ℝ)^(i-r)) / ((1+(2:ℝ)^i) * (1+(2:ℝ)^(i-r))) := by
  unfold Ep; rw [deriv_Φp]; simp only [Φp, logb]
  deriv_EQ fun r ↦ log (1 + 2 ^ (i - r)) / log 2 - log (1 + 2 ^ i) / log 2 + r * (2 ^ i / (1 + 2 ^ i))

lemma deriv_Em_r (hi : i < 0) :
    Set.EqOn (deriv (Em i)) (fun (r : ℝ) => ((2:ℝ)^i - (2:ℝ)^(i-r)) / ((1-(2:ℝ)^i) * (1-(2:ℝ)^(i-r)) )) (Set.Ioi 0) := by
  unfold Em Set.EqOn
  intro r hr
  rw[deriv_Φm hi]; simp only [Φm, logb]
  get_deriv (fun r ↦ -(log (1 - 2 ^ (i - r)) / log 2) + log (1 - 2 ^ i) / log 2 - r * (-2 ^ i / (1 - 2 ^ i))) within (Set.Ioi 0)
  simp only [Set.mem_Ici, List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, or_self, not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos,
    and_self, and_true, true_and, (by norm_num : (2 : ℝ) ≠ -1)]
  exact aux_inq1 hi
  simp only [toFun, zero_mul, zero_sub, neg_mul, one_mul, zero_add, sub_neg_eq_add,
    zero_div, mul_zero, sub_zero, Nat.cast_ofNat, rpow_two, add_zero, sub_self, neg_zero] at h
  rw[h.right r hr];
  simp only [Set.mem_Iio, Set.mem_Ioi] at hi hr
  have ie := one_minus_two_pow_ne_zero3 hi hr
  field_simp; simp only [aux_eq2]; field_simp; ring_nf

@[fun_prop]
lemma differentiable_Ep_r : Differentiable ℝ (Ep i) := by
  unfold Ep; rw [deriv_Φp]
  fun_prop (disch := simp)

@[fun_prop]
lemma continuous_Ep_r : Continuous (Ep i) := differentiable_Ep_r.continuous

@[fun_prop]
lemma differentiableOn_Em_r (hi : i < 0) : DifferentiableOn ℝ (Em i) (Set.Ioi 0) := by
  unfold Em; rw[deriv_Φm hi]
  have : ∀ x ∈ Set.Ioi 0, i - x < 0 := by
    simp only [Set.mem_Ioi, sub_neg]; intro x hx; linarith
  fun_prop (disch := assumption)

@[fun_prop]
lemma continuousOn_Em_r (hi : i < 0) : ContinuousOn (Em i) (Set.Ici 0) := by
  unfold Em; rw [deriv_Φm hi]; simp only [Φm, logb]
  have e := aux_inq2 hi
  have u : ∀ x ∈ Set.Ici 0, (2:ℝ) ≠ 0 ∨ 0 < i - x := by simp only [Set.mem_Ici, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, sub_pos, true_or, implies_true]
  fun_prop (disch := assumption)

/-
  Monotonicity properties of Ep(i, r) and Em(i, r) and their derivatives
  with respect to r
-/

lemma deriv_Ep_r_pos (hr : 0 < r) : 0 < deriv (Ep i) r := by
  simp only [deriv_Ep_r, ge_iff_le]
  have i3 : (2:ℝ) ^ i > 2 ^ (i - r) := by
    apply rpow_lt_rpow_of_exponent_lt; simp only [Nat.one_lt_ofNat]; linarith
  have i3: (2:ℝ) ^ i - 2 ^ (i - r) > 0 := by linarith
  positivity

lemma deriv_Em_r_pos (hi : i < 0) (hr : 0 < r) : 0 < deriv (Em i) r := by
  simp only [deriv_Em_r hi hr, gt_iff_lt]
  have i1 : (2:ℝ) ^ i < 1 := by
    apply rpow_lt_one_of_one_lt_of_neg _ hi; simp only [Nat.one_lt_ofNat]
  have _ : (2:ℝ) ^ (i-r) < 1 := by
    apply rpow_lt_one_of_one_lt_of_neg; simp only [Nat.one_lt_ofNat]; linarith
  have i3 : (2:ℝ) ^ i > 2 ^ (i - r) := by
    apply rpow_lt_rpow_of_exponent_lt; simp only [Nat.one_lt_ofNat]; linarith
  apply div_pos; linarith; apply mul_pos; linarith; linarith

lemma Ep_r_strictMonoOn : StrictMonoOn (Ep i) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  exact fun x => deriv_Ep_r_pos

lemma Ep_r_monotoneOn : MonotoneOn (Ep i) (Set.Ici 0) :=
  StrictMonoOn.monotoneOn Ep_r_strictMonoOn

lemma Em_r_strictMonoOn (hi : i < 0) : StrictMonoOn (Em i) (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop (disch := assumption))
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  exact fun x => deriv_Em_r_pos hi

lemma Em_r_monotoneOn (hi : i < 0) : MonotoneOn (Em i) (Set.Ici 0) :=
  StrictMonoOn.monotoneOn (Em_r_strictMonoOn hi)

lemma Ep_r_nonneg (hr : 0 ≤ r) : 0 ≤ (Ep i) r := by
  rw [← Ep_eq_zero i]
  apply Ep_r_monotoneOn _ hr hr
  simp only [Set.mem_Ici, le_refl]

lemma Ep_r_pos (hr : 0 < r) : 0 < (Ep i) r := by
  rw [← Ep_eq_zero i]
  apply Ep_r_strictMonoOn _ (le_of_lt hr) hr
  simp only [Set.mem_Ici, le_refl]

lemma Em_r_nonneg (hi : i < 0) (hr : 0 ≤ r) : 0 ≤ (Em i) r := by
  rw [← Em_eq_zero i]
  apply Em_r_monotoneOn hi _ hr hr
  simp only [Set.mem_Ici, le_refl]

lemma Em_r_pos (hi : i < 0) (hr : 0 < r) : 0 < (Em i) r := by
  rw [← Em_eq_zero i]
  apply Em_r_strictMonoOn hi _ (le_of_lt hr) hr
  simp only [Set.mem_Ici, le_refl]

lemma deriv_Ep_r_strictMono : StrictMonoOn (deriv (Ep r)) (Set.Ici 0) := by
  rw [deriv_Ep_r]
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop (disch := simp))
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx
  get_deriv (fun r_1 ↦ (2 ^ r - 2 ^ (r - r_1)) / ((1 + 2 ^ r) * (1 + 2 ^ (r - r_1)))) at x
  simp only [List.Forall, toFun, ne_eq, mul_eq_zero, one_plus_two_pow_ne_zero, or_self,
    not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos, and_self]
  simp only [toFun] at h
  rw[HasDerivAt.deriv h]; simp only [zero_mul, add_zero, zero_sub, neg_mul, one_mul, zero_add,
    sub_neg_eq_add, mul_neg, Nat.cast_ofNat, rpow_two, gt_iff_lt]
  have: (2 ^ (r - x) * log 2 * ((1 + 2 ^ r) * (1 + 2 ^ (r - x))) +
      (2 ^ r - 2 ^ (r - x)) * ((1 + 2 ^ r) * (2 ^ (r - x) * log 2))) /
    ((1 + 2 ^ r) * (1 + 2 ^ (r - x))) ^ 2 = 2 ^ (r - x) * log 2/ (1 + 2 ^ (r - x))^2 := by
    field_simp; ring_nf
  rw[this]; positivity

lemma deriv_Em_r_strictMono (hi : i < 0) : StrictMonoOn (deriv (Em i)) (Set.Ioi (0:ℝ)) := by
  have : ∀ x ∈ Set.Ioi 0, (2:ℝ) ≠ 0 ∨ 0 < i - x :=by simp only [Set.mem_Ioi, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, sub_pos, true_or, implies_true]
  have : ∀ x ∈ Set.Ioi 0, (1 - (2:ℝ) ^ i) * (1 - 2 ^ (i - x)) ≠ 0:=by
    intro x hx; simp only [Set.mem_Ioi, Set.mem_Iio] at hx hi
    have _: (2:ℝ) ^ i < 1 :=by apply rpow_lt_one_of_one_lt_of_neg _ hi; simp only [Nat.one_lt_ofNat]
    have _:  (2:ℝ) ^ (i-x) < 1 :=by apply rpow_lt_one_of_one_lt_of_neg; simp only [Nat.one_lt_ofNat]; linarith
    norm_num; constructor <;> linarith
  apply StrictMonoOn.congr _ (Set.EqOn.symm (deriv_Em_r hi))
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (by fun_prop (disch := assumption))
  intro x hx; simp only [interior_Ioi, Set.mem_Ioi, Set.mem_Iio] at hx hi
  have i1 : (2:ℝ) ^ i < 1 :=by apply rpow_lt_one_of_one_lt_of_neg _ hi; simp only [Nat.one_lt_ofNat]
  have i1 : 1 - (2:ℝ) ^ i ≠ 0:=by linarith
  have _ : (2:ℝ) ^ (i-x) < 1 :=by apply rpow_lt_one_of_one_lt_of_neg; simp only [Nat.one_lt_ofNat]; linarith
  have _ : 1 - (2:ℝ) ^ (i-x) > 0:=by linarith
  have i3 : (2:ℝ) ^ i > 2 ^ (i - x) :=by apply rpow_lt_rpow_of_exponent_lt; simp only [Nat.one_lt_ofNat]; linarith
  get_deriv (fun r ↦ (2 ^ i - 2 ^ (i - r)) / ((1 - 2 ^ i) * (1 - 2 ^ (i - r)))) at x
  simp only [List.Forall, toFun, ne_eq, mul_eq_zero, not_or, id_eq, gt_iff_lt, Nat.ofNat_pos,
    and_self, and_true]
  constructor <;> linarith
  simp only [toFun] at h; rw [HasDerivAt.deriv h]
  simp only [zero_mul, add_zero, zero_sub, neg_mul, one_mul, zero_add, sub_neg_eq_add, sub_self,
    Nat.cast_ofNat, rpow_two]
  have: (2 ^ (i - x) * log 2 * ((1 - 2 ^ i) * (1 - 2 ^ (i - x))) -
      (2 ^ i - 2 ^ (i - x)) * ((1 - 2 ^ i) * (2 ^ (i - x) * log 2))) /
    ((1 - 2 ^ i) * (1 - 2 ^ (i - x))) ^ 2 = 2 ^ (i - x) * log 2/(1 - 2 ^ (i - x))^2 :=by
    field_simp; ring_nf
  rw [this]; positivity

/-
  Continuity and differentiability of Ep(i, r) and Em(i, r) with respect to i
-/

private def fp (a : ℝ) := a * exp (-a) + exp (-a) - 1

private def gp a := exp (-a) + a - 1

@[fun_prop]
lemma differentiable_Ep_i: Differentiable ℝ (fun i => Ep i r) := by
  unfold Ep; rw [deriv_Φp]; fun_prop (disch := simp)

lemma differentiable_Em_i (hr : 0 ≤ r) : DifferentiableOn ℝ (fun i => Em i r) (Set.Iio 0) := by
  unfold Em
  have : ∀ i ∈ (Set.Iio 0), (fun i ↦ -Φm (i - r) + Φm i - r * deriv Φm i) i =
            (fun i ↦ -Φm (i - r) + Φm i - r * (-(2 : ℝ) ^ i / (1 - (2 : ℝ) ^ i))) i :=by
    intro i hi ; simp only [sub_right_inj, mul_eq_mul_left_iff]
    simp only [deriv_Φm hi, true_or]
  apply DifferentiableOn.congr _ this
  have : ∀ x ∈ Set.Iio 0, x - r < 0 := by
    simp only [Set.mem_Iio, sub_neg]; intro x x0; linarith
  have := one_minus_two_pow_ne_zero
  fun_prop (disch := first | assumption | simp)

private lemma deriv_Ep_i : deriv (fun i => Ep i r) =
    fun (i : ℝ) => 2 ^ i / ((1 + 2 ^ i) ^ 2 * (1 + 2 ^ (i - r))) * (2 ^ i * fp (log 2 * r) + gp (log 2 * r)) := by
  unfold Ep; rw [deriv_Φp]; simp only [Φp, logb, fp, gp]
  get_deriv fun i ↦ log (1 + 2 ^ (i - r)) / log 2 - log (1 + 2 ^ i) / log 2 + r * (2 ^ i / (1 + 2 ^ i))
  simp only [List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
    or_self, not_false_eq_true, id_eq, one_plus_two_pow_ne_zero, gt_iff_lt, Nat.ofNat_pos,
    and_self, implies_true, (by norm_num : (2 : ℝ) ≠ -1)]
  simp only [toFun, zero_mul, sub_zero, one_mul, zero_add, zero_div, mul_zero, Nat.cast_ofNat,
    rpow_two] at h
  simp only [h.right]; ext x; simp[aux_eq1, aux_eq2]; field_simp; ring_nf

private lemma deriv_Em_i (hr : 0 ≤ r) : Set.EqOn (deriv (fun i => Em i r))
    (fun (i : ℝ) => 2 ^ i / ((1 - 2 ^ i) ^ 2 * (1 - 2 ^ (i - r))) * (-(2 ^ i * fp (log 2 * r)) + gp (log 2 * r))) (Set.Iio 0) := by
  unfold Em Set.EqOn; intro i hi
  have : deriv (fun i ↦ -Φm (i - r) + Φm i - r * deriv Φm i) i =
        deriv (fun i ↦ -Φm (i - r) + Φm i - r * -(2 : ℝ) ^ i / (1 - (2 : ℝ) ^ i)) i := by
    apply deriv_EqOn_Iio _ hi; intro y hy; simp only [mul_neg, sub_right_inj]
    simp only [deriv_Φm hy]; field_simp
  rw[this]; simp only [Φm, logb, mul_neg, fp, neg_mul, gp]
  get_deriv (fun i ↦ -(log (1 - 2 ^ (i - r)) / log 2) + log (1 - 2 ^ i) / log 2 - -(r * 2 ^ i) / (1 - 2 ^ i)) within (Set.Iio 0)
  simp only [Set.mem_Iio, List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, or_self, not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos,
    and_self, and_true, true_and, (by norm_num : (2 : ℝ) ≠ -1)]
  intro x hx; exact aux_inq1' hx r hr
  simp only [toFun, zero_mul, sub_zero, one_mul, zero_add, zero_sub, zero_div,
    mul_zero, Nat.cast_ofNat, rpow_two, neg_mul, mul_neg, neg_neg] at h
  rw[h.right i hi];
  have ie := one_minus_two_pow_ne_zero4 hi hr
  have ie2 := one_minus_two_pow_ne_zero2 i hi
  field_simp
  simp[aux_eq1, aux_eq2]; field_simp; ring_nf
