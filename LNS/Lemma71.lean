import LNS.Common
import LNS.Basic
set_option maxHeartbeats 10000000

noncomputable section

open LNS
open Real
open Real Filter Topology

private def F (x:ℝ) (t:ℝ) := Φm (x - t) - Φm x

lemma F_t_StrictMono (hx : x < 0) : StrictMonoOn (F x) (Set.Ici (0:ℝ)) := by
  unfold F
  have ec2 : (fun y ↦ Φm (x - y)) = (fun y=> Φm y) ∘ (fun y=>x -y) :=by ext y; simp only [Function.comp_apply];
  apply strictMonoOn_of_deriv_pos_Ici0
  · apply ContinuousOn.sub _ (by apply continuousOn_const);
    rw[ec2];
    have:= DifferentiableOn.continuousOn differentiable_Φm
    apply ContinuousOn.comp this
    apply ContinuousOn.sub (by apply continuousOn_const) (by apply continuousOn_id);
    simp only [Set.MapsTo, Set.mem_Ici, Set.mem_Iio, sub_neg]; intro t ht; linarith
  · intro t ht
    rw[deriv_sub, deriv_const, deriv_comp_const_sub, deriv_Φm]; simp only [sub_zero, gt_iff_lt,Left.neg_pos_iff]
    apply div_neg_of_neg_of_pos (by simp only [Left.neg_neg_iff, Nat.ofNat_pos, rpow_pos_of_pos])
    simp only [sub_pos]; apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) (by linarith)
    simp only [Set.mem_Iio, sub_neg]; linarith
    rw[ec2]; apply DifferentiableAt.comp
    apply DifferentiableOn.differentiableAt differentiable_Φm (Iio_mem_nhds (by linarith))
    apply DifferentiableAt.sub (by apply differentiableAt_const) (by apply differentiableAt_id);
    simp only [differentiableAt_const]

lemma F_x_StrictMono (ht : 0 < t) : StrictMonoOn (fun x => F x t) (Set.Iio 0) := by
  unfold F
  have ec2 : (fun y ↦ Φm (y - t)) = (fun y=> Φm y) ∘ (fun y=>y-t) :=by ext y; simp only [Function.comp_apply];
  have:= DifferentiableOn.continuousOn differentiable_Φm
  apply strictMonoOn_of_deriv_pos (convex_Iio 0)
  · apply ContinuousOn.sub
    rw[ec2];
    apply ContinuousOn.comp this
    apply ContinuousOn.sub (by apply continuousOn_id) (by apply continuousOn_const) ;
    simp only [Set.MapsTo, Set.mem_Iic, Set.mem_Iio, sub_neg]; intro t ht; linarith
    apply ContinuousOn.mono this
    exact subset_refl _
  · intro x hx; simp only [interior_Iio, Set.mem_Iio] at hx
    rw[deriv_sub, deriv_comp_sub_const, deriv_Φm, deriv_Φm];
    simp only
    have : 1 - (2:ℝ)^x > 0 :=by simp only [gt_iff_lt, sub_pos]; apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) (by linarith)
    have : 1 - (2:ℝ)^(x-t) > 0 :=by simp only [gt_iff_lt, sub_pos]; apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) (by linarith)
    have : (2:ℝ)^x - (2:ℝ)^(x-t) > 0 :=by simp only [gt_iff_lt, sub_pos, Nat.one_lt_ofNat, rpow_lt_rpow_left_iff, sub_lt_self_iff]; exact ht
    have : - (2:ℝ) ^ (x - t) / (1 - 2 ^ (x - t)) - -2 ^ x / (1 - 2 ^ x) = (2^x - 2^ (x-t)) / ((1 -2 ^ x)* (1 -2 ^ (x-t)) ):=by
      field_simp; ring_nf
    rw[this]; positivity
    simp only [Set.mem_Iio]; linarith; simp only [Set.mem_Iio, sub_neg]; linarith
    rw[ec2]; apply DifferentiableAt.comp
    apply DifferentiableOn.differentiableAt differentiable_Φm (Iio_mem_nhds (by linarith))
    simp only [differentiableAt_id', differentiableAt_const, DifferentiableAt.sub]
    apply DifferentiableOn.differentiableAt differentiable_Φm (Iio_mem_nhds (by linarith))

lemma F_x_Monotone (ht : 0 ≤ t) : MonotoneOn (fun x => F x t) (Set.Iio 0) := by
  cases le_iff_lt_or_eq.mp ht with
  | inl ht =>
    exact (F_x_StrictMono ht).monotoneOn
  | inr ht =>
    simp only [← ht, F, sub_zero, sub_self]
    exact monotoneOn_const

lemma max_of_F (hx₀ : x₀ < 0) (hx : x ≤ x₀) (ht : 0 ≤ t) (htp : t ≤ m) :
    F x t ≤ F x₀ m := by
  have first : F x t ≤ F x₀ t := F_x_Monotone ht (by linarith : x < 0) hx₀ hx
  have second : F x₀ t ≤ F x₀ m := (F_t_StrictMono hx₀).monotoneOn ht (by linarith : 0 ≤ m) htp
  linarith

lemma Φm_strictAnti : StrictAntiOn Φm (Set.Iio 0):= by
  apply strictAntiOn_of_deriv_neg (convex_Iio 0)
  exact DifferentiableOn.continuousOn differentiable_Φm
  simp only [interior_Iio]; intro t ht; simp only [deriv_Φm ht]
  simp only [Set.mem_Iio] at ht
  apply div_neg_of_neg_of_pos; simp only [Left.neg_neg_iff, Nat.ofNat_pos, rpow_pos_of_pos]
  simp only [gt_iff_lt, sub_pos]; apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) (by linarith)


lemma Lemma71 (hx₀ : x₀ < 0) (hx : x ≤ x₀) (hy : y ≤ x₀) (hd : |x - y| ≤ m) :
    |Φm x - Φm y| ≤ Φm (x₀ - m) - Φm x₀ := by
  wlog h : x ≤ y generalizing x y
  · rw [abs_sub_comm]
    apply this hy hx _ (by linarith)
    rw [abs_sub_comm]; exact hd
  have lhs_eq1 : |Φm x - Φm y| = Φm x - Φm y := by
    apply abs_of_nonneg; simp only [sub_nonneg]
    exact StrictAntiOn.antitoneOn Φm_strictAnti (by linarith : x < 0) (by linarith : y < 0) h
  have lhs_eq2 : Φm x - Φm y = F y (y - x) := by unfold F; rw [sub_sub_cancel]
  have rhs_eq : Φm (x₀ - m) - Φm x₀ = F x₀ m := by unfold F; simp only
  rw [rhs_eq, lhs_eq1, lhs_eq2]
  apply max_of_F hx₀ hy (by linarith)
  rw [abs_le] at hd; linarith
