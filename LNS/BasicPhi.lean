import LNS.Common
import LNS.Tactic
import LNS.Definitions

namespace LNS

noncomputable section

open Real

/-
  Inequalities for fun_prop
-/

@[simp]
lemma one_plus_two_pow_pos (x : ℝ) : 0 < 1 + (2 : ℝ) ^ x := by
  linarith [rpow_pos_of_pos two_pos x]

@[simp]
lemma one_plus_two_pow_ne_zero (x : ℝ) : 1 + (2 : ℝ) ^ x ≠ 0 := by
  linarith [rpow_pos_of_pos two_pos x]

@[simp]
lemma one_minus_two_pow_ne_zero2 :  ∀ x < (0:ℝ),  1 - (2:ℝ) ^ x ≠ 0 := by
  intro x hx
  have ieq : (2:ℝ) ^ x < 1:=by refine rpow_lt_one_of_one_lt_of_neg ?hx hx; linarith
  linarith

-- @[simp]
-- lemma one_minus_two_pow_ne_zero : ∀ x ∈ Set.Iio (0:ℝ),  1 - (2:ℝ) ^ x ≠ 0 :=by
--   simp only [Set.mem_Iio, ne_eq] ;  exact one_minus_two_pow_ne_zero2

-- @[simp]
-- lemma two_ne_zero :  ∀ x ∈ Set.Iio (0:ℝ),  (2:ℝ)  ≠ (0:ℝ)  :=by
--   simp only [Set.mem_Iio, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, implies_true]

/-
  Properties of Φp
-/

@[fun_prop]
lemma differentiable_Φp : Differentiable ℝ Φp := by
  unfold Φp logb;
  fun_prop (disch := simp)

@[fun_prop]
lemma continuous_Φp : Continuous Φp := differentiable_Φp.continuous

lemma deriv_Φp : deriv Φp = fun (x : ℝ) => (2 : ℝ) ^ x / (1 + (2 : ℝ) ^ x) := by
  unfold Φp logb
  deriv_EQ fun x ↦ log (1 + 2 ^ x) / log 2

lemma deriv2_Φp : deriv (deriv Φp) = fun x => (2 : ℝ) ^ x * log 2 / (1 + (2 : ℝ) ^ x) ^ 2 := by
  simp only [deriv_Φp]
  deriv_EQ (fun x ↦ 2 ^ x / (1 + 2 ^ x))

lemma deriv_Φp_pos : (deriv Φp) x > 0 := by
  simp only [deriv_Φp]; positivity

lemma deriv2_Φp_pos :  deriv (deriv Φp) x > 0 := by
  simp only [deriv2_Φp]; positivity

/-
  Properties of Φm
-/

lemma differentiable_Φm : DifferentiableOn ℝ Φm (Set.Iio (0:ℝ)) := by
  unfold Φm
  fun_prop (disch := simp)

@[fun_prop]
lemma continuous_Φm : ContinuousOn Φm (Set.Iio 0) := differentiable_Φm.continuousOn

lemma deriv_Φm : Set.EqOn (deriv Φm) (fun x=> -(2 : ℝ) ^ x / (1 - (2 : ℝ) ^ x)) (Set.Iio (0:ℝ)) := by
  unfold Φm logb
  get_deriv (fun x ↦ log (1 - 2 ^ x) / log 2) within (Set.Iio (0:ℝ))
  simp only [Set.mem_Iio, List.Forall, toFun, ne_eq, log_eq_zero, OfNat.ofNat_ne_zero,
    OfNat.ofNat_ne_one, numineq, or_self, not_false_eq_true, id_eq, gt_iff_lt, Nat.ofNat_pos,
    and_self, and_true, true_and]
  exact one_minus_two_pow_ne_zero2
  simp only [toFun, Set.mem_Iio, deriv_div_const, zero_mul, one_mul, zero_add, zero_sub, zero_div,
    mul_zero, sub_zero, Nat.cast_ofNat, rpow_two] at h
  simp only [Set.EqOn, Set.mem_Iio, deriv_div_const]
  intro x hx
  simp only [h.right x hx]; field_simp; ring_nf

lemma deriv2_Φm : Set.EqOn (deriv (deriv Φm)) (fun x => -(log 2 *(2 : ℝ) ^ x ) / (1 - (2 : ℝ) ^ x)^2) (Set.Iio (0:ℝ)) := by
  unfold Set.EqOn
  intro x hx
  rw[deriv_EqOn_Iio deriv_Φm hx]
  get_deriv (fun x ↦ -2 ^ x / (1 - 2 ^ x)) within (Set.Iio (0:ℝ))
  simp only [Set.mem_Iio, List.Forall, toFun, ne_eq, id_eq, gt_iff_lt, Nat.ofNat_pos, and_self, and_true]
  exact one_minus_two_pow_ne_zero2
  simp only [toFun, zero_mul, one_mul, zero_add, neg_mul, zero_sub, mul_neg, neg_neg,
    Nat.cast_ofNat, rpow_two] at h
  simp only [h.right x hx]; field_simp; ring_nf
