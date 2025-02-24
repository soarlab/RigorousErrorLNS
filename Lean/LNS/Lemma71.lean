import LNS.Definitions
import LNS.BasicPhi

namespace LNS

open Real

private noncomputable def F (x:ℝ) (t:ℝ) := Φm (x - t) - Φm x

private lemma F_t_StrictMono (hx : x < 0) : StrictMonoOn (F x) (Set.Ici 0) := by
  unfold F
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · have : ∀ y ∈ Set.Ici 0, x - y < 0 := by
      simp only [Set.mem_Ici, sub_neg]; intro y ys; linarith
    fun_prop (disch := assumption)
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro t ht
    have hxt : x - t < 0 := by linarith
    rw [deriv_sub (by fun_prop (disch := assumption)) (by fun_prop)]
    rw [deriv_comp_const_sub, deriv_Φm hxt, deriv_const]
    simp only [sub_zero, Left.neg_pos_iff, gt_iff_lt]
    apply div_neg_of_neg_of_pos (by simp only [Left.neg_neg_iff, Nat.ofNat_pos, rpow_pos_of_pos])
    simp only [sub_pos]; apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) (by linarith)

private lemma F_x_StrictMono (ht : 0 < t) : StrictMonoOn (fun x => F x t) (Set.Iio 0) := by
  unfold F
  apply strictMonoOn_of_deriv_pos (convex_Iio 0)
  · have : ∀ x ∈ Set.Iio 0, x - t < 0 := by
      simp only [Set.mem_Iio]; intro x hx; linarith
    fun_prop (disch := assumption)
  simp only [interior_Iio, Set.mem_Iio]
  intro x hx
  have hxt : x - t < 0 := by linarith
  rw [deriv_sub (by fun_prop (disch := assumption)) (by fun_prop (disch := assumption))]
  rw [deriv_comp_sub_const, deriv_Φm hxt, deriv_Φm hx]
  simp only [sub_pos, gt_iff_lt, neg_div, neg_lt_neg_iff]
  apply div_lt_div₀
  · exact rpow_lt_rpow_of_exponent_lt one_lt_two (by linarith : x - t < x)
  · rw [sub_le_sub_iff_left]
    exact rpow_le_rpow_of_exponent_le one_le_two (by linarith : x - t ≤ x)
  · positivity
  · rw [sub_pos]
    exact rpow_lt_one_of_one_lt_of_neg one_lt_two hx

private lemma F_x_MonotoneOn (ht : 0 ≤ t) : MonotoneOn (fun x => F x t) (Set.Iio 0) := by
  cases le_iff_lt_or_eq.mp ht with
  | inl ht =>
    exact (F_x_StrictMono ht).monotoneOn
  | inr ht =>
    simp only [← ht, F, sub_zero, sub_self]
    exact monotoneOn_const

private lemma max_of_F (hx₀ : x₀ < 0) (hx : x ≤ x₀) (ht : 0 ≤ t) (htp : t ≤ m) :
    F x t ≤ F x₀ m := by
  have first : F x t ≤ F x₀ t := F_x_MonotoneOn ht (by linarith : x < 0) hx₀ hx
  have second : F x₀ t ≤ F x₀ m := (F_t_StrictMono hx₀).monotoneOn ht (by linarith : 0 ≤ m) htp
  linarith

lemma Lemma71 (hx₀ : x₀ < 0) (hx : x ≤ x₀) (hy : y ≤ x₀) (hd : |x - y| ≤ m) :
    |Φm x - Φm y| ≤ Φm (x₀ - m) - Φm x₀ := by
  wlog h : x ≤ y generalizing x y
  · rw [abs_sub_comm]
    apply this hy hx _ (by linarith)
    rw [abs_sub_comm]; exact hd
  have lhs_eq1 : |Φm x - Φm y| = Φm x - Φm y := by
    apply abs_of_nonneg; simp only [sub_nonneg]
    exact StrictAntiOn.antitoneOn Φm_strictAntiOn (by linarith : x < 0) (by linarith : y < 0) h
  have lhs_eq2 : Φm x - Φm y = F y (y - x) := by unfold F; rw [sub_sub_cancel]
  have rhs_eq : Φm (x₀ - m) - Φm x₀ = F x₀ m := by unfold F; simp only
  rw [rhs_eq, lhs_eq1, lhs_eq2]
  apply max_of_F hx₀ hy (by linarith)
  rw [abs_le] at hd; linarith
