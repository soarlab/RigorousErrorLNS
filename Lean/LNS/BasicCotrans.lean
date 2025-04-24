import LNS.Definitions
import LNS.BasicIxRx
import LNS.BasicRounding
import LNS.BasicPhi

namespace LNS

noncomputable section

open Real

private noncomputable def g_aux (x:ℝ) (t:ℝ) := Φm (x - t) - Φm x

private lemma g_aux_t_StrictMono (hx : x < 0) : StrictMonoOn (g_aux x) (Set.Ici 0) := by
  unfold g_aux
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

private lemma g_aux_x_StrictMono (ht : 0 < t) : StrictMonoOn (fun x => g_aux x t) (Set.Iio 0) := by
  unfold g_aux
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

private lemma g_aux_x_MonotoneOn (ht : 0 ≤ t) : MonotoneOn (fun x => g_aux x t) (Set.Iio 0) := by
  cases le_iff_lt_or_eq.mp ht with
  | inl ht =>
    exact (g_aux_x_StrictMono ht).monotoneOn
  | inr ht =>
    simp only [← ht, g_aux, sub_zero, sub_self]
    exact monotoneOn_const

private lemma max_of_g_aux (hx₀ : x₀ < 0) (hx : x ≤ x₀) (ht : 0 ≤ t) (htp : t ≤ m) :
    g_aux x t ≤ g_aux x₀ m := by
  have first : g_aux x t ≤ g_aux x₀ t := g_aux_x_MonotoneOn ht (by linarith : x < 0) hx₀ hx
  have second : g_aux x₀ t ≤ g_aux x₀ m := (g_aux_t_StrictMono hx₀).monotoneOn ht (by linarith : 0 ≤ m) htp
  linarith

lemma cotrans_lemma (hx₀ : x₀ < 0) (hx : x ≤ x₀) (hy : y ≤ x₀) (hd : |x - y| ≤ m) :
    |Φm x - Φm y| ≤ Φm (x₀ - m) - Φm x₀ := by
  wlog h : x ≤ y generalizing x y
  · rw [abs_sub_comm]
    apply this hy hx _ (by linarith)
    rw [abs_sub_comm]; exact hd
  have lhs_eq1 : |Φm x - Φm y| = Φm x - Φm y := by
    apply abs_of_nonneg; simp only [sub_nonneg]
    exact StrictAntiOn.antitoneOn Φm_strictAntiOn (by linarith : x < 0) (by linarith : y < 0) h
  have lhs_eq2 : Φm x - Φm y = g_aux y (y - x) := by unfold g_aux; rw [sub_sub_cancel]
  have rhs_eq : Φm (x₀ - m) - Φm x₀ = g_aux x₀ m := by unfold g_aux; simp only
  rw [rhs_eq, lhs_eq1, lhs_eq2]
  apply max_of_g_aux hx₀ hy (by linarith)
  rw [abs_le] at hd; linarith

lemma phi_sub_phi_nonneg (hx : 0 ≤ x) : 0 ≤ Φm (-1 - x) - Φm (-1) := by
  apply sub_nonneg_of_le
  exact Φm_antitoneOn (by simp; linarith) (by simp) (by linarith)

lemma phi_sub_phi_bound (he : 0 < e) : Φm (-1 - e) - Φm (-1) < e := by
  set f := fun x => x - Φm (-1 - x)
  suffices h : f 0 < f e by simp [f] at h; linarith
  have : ∀ x ∈ Set.Ici (0 : ℝ), -1 - x < 0 := by simp only [Set.mem_Ici]; intro x hx; linarith
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) _ _ Set.left_mem_Ici (le_of_lt he) he
  · unfold f; fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi, f]
  intro x hx
  rw [deriv_sub (by fun_prop) (by fun_prop (disch := linarith))]
  have eq : (fun x => Φm (-1 - x)) = (fun x => Φm ((-1) * x + (-1))) := by
    ext x; congr 1; linarith
  rw [eq, deriv_comp_linear, deriv_Φm (by simp; linarith)]
  have : 1 - (2 : ℝ) ^ (-x + -1) > 0 := by
    simp only [gt_iff_lt, sub_pos]
    apply rpow_lt_one_of_one_lt_of_neg one_lt_two
    linarith
  field_simp
  apply lt_sub_left_of_add_lt
  rw [← mul_two]
  nth_rewrite 2 [(by norm_num : 2 = (2 : ℝ) ^ (1 : ℝ))]
  rw [← rpow_add zero_lt_two]
  apply rpow_lt_one_of_one_lt_of_neg one_lt_two
  linarith

lemma phi_sub_phi_bound' (he : 0 ≤ e) : Φm (-1 - e) - Φm (-1) ≤ e := by
  cases le_iff_eq_or_lt.mp he with
  | inl h => rw [← h, Φm, Φm]; norm_num
  | inr h => exact le_of_lt (phi_sub_phi_bound h)

lemma k_neg (hd : 0 < Δ) (hx : x < 0) : kval Δ x < 0 := by
  have i1 : ind Δ x < x := ind_lt_x hd
  have : Φm (rem Δ x) < Φm (ind Δ x) := by
    apply Φm_strictAntiOn (by linarith : ind Δ x < 0) (rem_lt_zero hd)
    apply lt_of_sub_neg
    rw [ind_sub_rem]; exact hx
  unfold kval; linarith

lemma contrasformation_arnold {a b : ℝ} (ha : a < 0) (hb : b < 0) :
    Φm (b + a) = Φm b + Φp (b + Φm a - Φm b) := by
  unfold Φp
  rw [rpow_sub zero_lt_two, rpow_add zero_lt_two, two_rpow_Φm ha, two_rpow_Φm hb]
  have ha1 := one_sub_two_pow_pos ha
  have hb1 := one_sub_two_pow_pos hb
  unfold Φm
  rw [← logb_mul (by positivity) (by positivity)]
  congr
  field_simp
  rw [rpow_add zero_lt_two]
  ring

-- lemma contrasformation_coleman {a b : ℝ} (ha : 0 < a) (hb : b < 0) :
--     Φm (b - a) = Φm b + Φm (b - a - Φm b + Φm a) := by
--   nth_rw 3 [show ∀ x, Φm x = logb 2 (1 - 2 ^ x) from fun _ => rfl]
--   rw [rpow_sub zero_lt_two, rpow_add, @two_rpow_Φm (-a) (by linarith), two_rpow_Φm hb]
--   have ha1 := @one_sub_two_pow_pos (-a) (by linarith)
--   have hb1 := one_sub_two_pow_pos hb
--   unfold Φm
--   rw [← logb_mul (by positivity) (by sorry)]
--   congr
--   rw [rpow_sub zero_lt_two]
--   field_simp [rpow_neg, ← one_div]
--   ring_nf
--   sorry


lemma cotransformation (hd : 0 < Δ) (hx : x < 0) : Φm x = Φm (ind Δ x) + Φm (kval Δ x) := by
  unfold Φm
  have ineq : ∀ {y : ℝ}, y < 0 → (2:ℝ) ^ y < 1 := by
    intro y hy; exact rpow_lt_one_of_one_lt_of_neg one_lt_two hy
  have i0 : (2:ℝ) ^ x < 1 := ineq hx
  have i1 : (2:ℝ) ^ ind Δ x < 1 := ineq (ind_lt_zero hd hx)
  have i2 : (2:ℝ) ^ kval Δ x < 1 := ineq (k_neg hd hx)
  have i3 : (2:ℝ) ^ rem Δ x < 1 := ineq (rem_lt_zero hd)
  unfold logb; field_simp
  apply Real.exp_eq_exp.mp
  rw [exp_log (by linarith), exp_add, exp_log (by linarith), exp_log (by linarith)]
  set a := (2:ℝ) ^ rem Δ x
  set b := (2:ℝ) ^ ind Δ x
  have eq : 2 ^ kval Δ x = 2 ^ x * (1 - a) / (1 - b) := by
    unfold kval Φm; rw [rpow_add, rpow_sub, rpow_logb, rpow_logb]; field_simp
    any_goals linarith
  rw [eq]; field_simp [(by linarith : 1 - b ≠ 0)]; ring_nf
  have eq : (2:ℝ) ^ x * a = b := by
    rw [← rpow_add zero_lt_two]; unfold rem; simp [b]
  rw [eq]; ring

private def f_aux (x : ℝ) := x - Φm x

private lemma f_aux_strictMono : StrictMonoOn f_aux (Set.Iio 0) := by
  unfold f_aux
  apply strictMonoOn_of_deriv_pos (convex_Iio _) (by fun_prop)
  · simp only [interior_Iio, Set.mem_Iio, differentiableAt_id']
    intro x hx
    rw [deriv_sub differentiableAt_id' (differentiable_Φm.differentiableAt (Iio_mem_nhds hx))]
    rw [deriv_id'', deriv_Φm hx]
    simp only [sub_pos]
    have : 1 - (2 : ℝ) ^ x > 0 := by
      simp only [gt_iff_lt, sub_pos]
      exact rpow_lt_one_of_one_lt_of_neg one_lt_two hx
    rw [div_lt_one this]
    linarith

private lemma k_bound_eq (hd : 0 < d) : Φm (-2 * d) - Φm (-d) = Φp (-d) := by
  unfold Φm Φp
  have neg_d : -d < 0 ∧ -2 * d < 0 := by constructor <;> linarith
  have ineq_d := one_minus_two_pow_ne_zero2 _ neg_d.1
  rw [← logb_div (one_minus_two_pow_ne_zero2 _ neg_d.2) ineq_d]
  have : 1 - (2 : ℝ) ^ (-2 * d) = (1 - (2 : ℝ) ^ (-d)) * (1 + (2 : ℝ) ^ (-d)) := by
    rw [(by linarith : -2 * d = (-d) * 2), rpow_mul]
    ring_nf; simp only [rpow_two]
    norm_num
  rw [this]
  field_simp

private lemma k_bound_ineq (hd : 0 < d) : -d - Φp (-d) ≤ -d / 2 - 1 := by
  apply (by intros; linarith : forall a b : ℝ, 1 ≤ b + a / 2 → -a - b ≤ -a / 2 - 1)
  set f := fun x => Φp (-x) + x / 2
  suffices h : 1 ≤ f d from h
  rw [(by norm_num [f, Φp] : 1 = f 0)]
  suffices h : MonotoneOn f (Set.Ici 0) from h (le_refl (0 : ℝ)) (le_of_lt hd) (le_of_lt hd)
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi, f]
  intro x hx
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_comp_neg, deriv_Φp]
  simp only [deriv_div_const, deriv_id'', le_neg_add_iff_add_le, add_zero]
  rw [div_le_div_iff₀ (one_plus_two_pow_pos (-x)) (by norm_num)]
  apply (by intros; linarith : forall a : ℝ, a ≤ 1 → a * 2 ≤ 1 * (1 + a))
  exact rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith)

lemma k_bound (hd : 0 < Δ) (hx : x ≤ -Δ) : kval Δ x ≤ -Δ - Φp (-Δ) := by
  unfold kval
  nth_rewrite 1 [← ind_sub_rem Δ x]
  set a := rem _ _
  set b := ind _ _
  have bx : b < x := ind_lt_x hd
  have b0 : b < 0 := by linarith
  have a0 : a < 0 := rem_lt_zero hd
  have eq : forall c d, b - a - c + d = (b - c) - (a - d) := by intros; ring
  rw [eq, ← f_aux, ← f_aux]
  have ineq1 : f_aux b ≤ f_aux (-2 * Δ) := by
    apply f_aux_strictMono.monotoneOn b0 (by linarith : -2 * Δ < 0)
    exact ind_le_two_delta hd hx
  have ineq2 : f_aux (-Δ) ≤ f_aux a := by
    apply f_aux_strictMono.monotoneOn (by linarith : -Δ < 0) a0
    exact rem_ge_neg_delta hd
  apply le_trans (by linarith : f_aux b - f_aux a ≤ f_aux (-2 * Δ) - f_aux (-Δ))
  unfold f_aux
  have eq : forall a b c : ℝ, -2 * a - b - (-a - c) = -a - (b - c) := by intros; ring
  rw [eq, k_bound_eq hd]

lemma k_bound' (hd : 0 < Δ) (hx : x ≤ -Δ) : kval Δ x ≤ -Δ / 2 - 1 :=
  le_trans (k_bound hd hx) (k_bound_ineq hd)

lemma k_bound'' (hd : 0 < Δ) (hx : x ≤ -Δ) : kval Δ x ≤ -1 := by
  apply le_trans (k_bound' hd hx); linarith

lemma krnd_fix_bound (fix : FixedPoint) (Δ x : ℝ) : |kval Δ x - krnd fix Δ x| ≤ 2 * fix.ε := by
  set a1 := fix.rnd (Φm (ind Δ x)) - Φm (ind Δ x)
  set a2 := Φm (rem Δ x) - fix.rnd (Φm (rem Δ x))
  have eq : kval Δ x - krnd fix Δ x = a1 + a2 := by unfold kval krnd; ring_nf
  rw [eq]
  apply le_trans (abs_add _ _)
  have i1 : |a1| ≤ fix.ε := by apply fix.hrnd_sym
  have i2 : |a2| ≤ fix.ε := by apply fix.hrnd
  linarith

lemma krnd_bound (fix : FixedPoint) {Δ x : ℝ} (hd : 0 < Δ) (hx : x ≤ -Δ) :
    krnd fix Δ x ≤ -Δ / 2 - 1 + 2 * fix.ε := by
  have ineq1 := (abs_le.mp (krnd_fix_bound fix Δ x)).1
  have ineq2 := k_bound' hd hx
  linarith

lemma krnd_fix_bound_dir (fix : FixedPointDir) (Δ x : ℝ) : |kval Δ x - krnd fix Δ x| ≤ fix.ε := by
  set a1 := Φm (ind Δ x) - fix.rnd (Φm (ind Δ x))
  set a2 := Φm (rem Δ x) - fix.rnd (Φm (rem Δ x))
  have eq : kval Δ x - krnd fix Δ x = a2 - a1 := by unfold kval krnd; ring_nf
  rw [eq]
  apply fix.abs_rnd_sub_rnd

lemma krnd_bound_dir (fix : FixedPointDir) {Δ x : ℝ} (hd : 0 < Δ) (hx : x ≤ -Δ) :
    krnd fix Δ x ≤ -Δ / 2 - 1 + fix.ε := by
  have ineq1 := (abs_le.mp (krnd_fix_bound_dir fix Δ x)).1
  have ineq2 := k_bound' hd hx
  linarith
