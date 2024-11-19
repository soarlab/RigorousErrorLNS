import LNS.Tactic
import LNS.Definitions
import LNS.BasicErrCorrection

namespace LNS

open Real

noncomputable section

private def Gp a b := Fp b a / deriv (Fp b) a

private def K a b := a * a * log (a + b) - a * a * log (a + 1) - a * b + a + b * log b + b * log (a + 1) - b * log (a + b)

private lemma deriv_K (ha : 0 < a) : Set.EqOn (deriv (K a))
    (fun b => (a * a) / (a + b) - a - b / (a + b) + log b + log (a + 1) - log (a + b) + 1) (Set.Ioi 0) := by
  unfold K
  get_deriv (fun b ↦ a * a * log (a + b) - a * a * log (a + 1) - a * b + a + b * log b + b * log (a + 1) - b * log (a + b))
      within (Set.Ioi 0)
  simp only [Set.mem_Ioi, List.Forall, toFun, ne_eq, id_eq]
  intro x hx; split_ands <;> linarith
  simp only [toFun] at h
  intro b hb
  rw [h.right b hb]
  simp only [Set.mem_Ioi] at hb
  have : a + 1 ≠ 0 := by linarith
  have : a + b ≠ 0 := by linarith
  field_simp; ring_nf

private lemma deriv2_K (ha : 0 < a) : Set.EqOn (deriv (deriv (K a)))
      (fun b => (a * a) * (1 - b) / (b * (a + b) ^ 2)) (Set.Ioi 0) := by
  have e : Set.EqOn (deriv (K a))
      (fun b=> (a*a)/(a+b) - a - b/(a+b) + log b + log (a+1) - log (a+b) + (1:ℝ)) (Set.Ioi 0) := by
    apply Set.EqOn.mono _ (deriv_K ha)
    exact subset_refl _
  intro b hb; rw [deriv_EqOn_Ioi e hb]
  simp only [Set.mem_Ioi] at hb
  get_deriv (fun b ↦ a * a / (a + b) - a - b / (a + b) + log b + log (a + 1) - log (a + b) + 1) within (Set.Ioi 0)
  simp only [Set.mem_Ioi, List.Forall, toFun, ne_eq, id_eq, and_self_left]
  intro x hx; split_ands <;> linarith
  simp only [toFun] at h
  rw [h.right b hb]
  have : a + 1 ≠ 0 := by linarith
  have : a + b ≠ 0 := by linarith
  field_simp; ring_nf

private lemma deriv_K_strictAnti (ha : 0 < a) : StrictAntiOn (deriv (K a)) (Set.Ici 1) := by
  have hsub : Set.Ici (1 : ℝ) ⊆ Set.Ioi 0 := by
    intro x; simp only [Set.mem_Ici, Set.mem_Ioi]; intro h; linarith
  apply strictAntiOn_of_deriv_neg (convex_Ici 1)
  · apply ContinuousOn.congr _ ((deriv_K ha).mono hsub)
    have : ∀ x ∈ Set.Ici 1, a + x ≠ 0 := by
      simp only [Set.mem_Ici, ne_eq]
      intro x hx; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ), x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intro x hx; linarith
    fun_prop (disch := assumption)
  · intro b hb; simp only [Set.nonempty_Iio, interior_Ici'] at hb
    have hb' : b > 0 := by simp only [Set.mem_Ioi] at hb; linarith
    simp only [deriv2_K ha hb']
    simp only [Set.mem_Ioi] at hb
    have : a * a * (1 - b) / (b * (a + b) ^ 2) =  - (a * a * (b-1) / (b * (a + b) ^ 2)) := by ring_nf
    simp only [this, Left.neg_neg_iff, gt_iff_lt]
    have : b - 1 > 0 := by linarith
    positivity

private lemma deriv_K_neg (ha : 0 < a) (hb : 1 < b) : deriv (K a) b < 0 := by
  have : deriv (K a) 1 = 0 := by
    have : (1 : ℝ) ∈ Set.Ioi 0 := by simp only [Set.mem_Ioi, zero_lt_one]
    rw [deriv_K ha this]
    have : a + 1 > 0 := by linarith
    field_simp; ring_nf
  rw [← this]
  apply (deriv_K_strictAnti ha) (by simp only [Set.mem_Ici, le_refl]) (by simp only [Set.mem_Ici]; linarith) hb

private lemma K_strictAnti (ha : 0 < a) : StrictAntiOn (K a) (Set.Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1)
  unfold K
  have : ∀ x ∈ Set.Ici 1, a + x ≠ 0 := by
    simp only [Set.mem_Ici, ne_eq]
    intro x hx; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ), x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intro x hx; linarith
  fun_prop (disch := assumption)
  intro b hb
  apply deriv_K_neg ha; simp only [Set.nonempty_Iio, interior_Ici'] at hb; exact hb

private lemma K_neg (ha : 0 < a) (hb : 1 < b) : K a b < 0 := by
  have : K a 1 = 0 := by simp only [K, sub_self, mul_one, zero_sub, neg_add_cancel, log_one,
    mul_zero, add_zero, one_mul, zero_add]
  rw [← this]
  apply (K_strictAnti ha) (by simp only [Set.mem_Ici, le_refl]) _ hb
  simp only [Set.mem_Ici]; linarith

private lemma deriv_Gp_b_neg (ha : 0 < a) (hb : 1 < b) : deriv (Gp a) b < 0 := by
  have hb0 : b > 0 := by linarith
  unfold Gp
  rw [deriv_div]
  · have : deriv (Fp b) a ^ 2 > 0 := by apply pow_pos (deriv_Fp_a_pos ha hb)
    apply div_neg_of_neg_of_pos _ this
    rw [deriv_Fp_a_b ha hb0, deriv_Fp_b ha hb0, deriv_Fp_a hb0 ha]
    unfold Fp
    simp only
    have : a + b > 0 := by linarith
    have : a * (b - 1) / (b * (a + b)) * ((a + 1) / (a + b) - 1 - log (a + 1) + log (a + b)) -
      (-(a + 1) * log (a + 1) + (a + 1) * log (a + b) - log b) * ((b - 1) / (a + b) ^ 2)
      = (b-1)/(b*(a+b)^2)* (K a b) := by unfold K; field_simp; ring_nf
    rw [this]; apply mul_neg_of_pos_of_neg
    · have : b - 1 > 0 := by linarith
      have : a + b > 0 := by linarith
      positivity
    · apply K_neg ha hb
  · exact differentiable_Fp_b ha hb0
  · exact differentiable_Fp_a_b ha hb0
  · apply ne_of_gt (deriv_Fp_a_pos ha hb)

private lemma strictAntiOn_Gp_b (ha : 0 < a) : StrictAntiOn (Gp a) (Set.Ioi 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 1)
  unfold Gp
  apply ContinuousOn.div
  apply continuousOn_of_forall_continuousAt
  intro b hb
  have hb0 : b > 0 := by simp only [Set.mem_Ioi] at hb; linarith
  apply DifferentiableAt.continuousAt (differentiable_Fp_b ha hb0)
  apply continuousOn_of_forall_continuousAt
  intro b hb
  have hb0 : b > 0 := by simp only [Set.mem_Ioi] at hb; linarith
  apply DifferentiableAt.continuousAt (differentiable_Fp_a_b ha hb0)
  intro b hb; apply ne_of_gt (deriv_Fp_a_pos ha hb)
  intro b hb; simp only [interior_Ioi, Set.mem_Ioi] at hb; exact deriv_Gp_b_neg ha hb

lemma deriv_Fp_div_pos (ha : 0 < a) (hb : 1 < b) (hc : b < c) :
    deriv (fun a ↦ Fp b a / Fp c a) a < 0 := by
  have ie : Gp a b > Gp a c := by apply strictAntiOn_Gp_b ha hb (by simp only [Set.mem_Ioi]; linarith) hc
  unfold Gp at ie
  have i1 : deriv (Fp b) a > 0 := by apply deriv_Fp_a_pos ha hb
  have i2 : deriv (Fp c) a > 0 := by apply deriv_Fp_a_pos ha; linarith
  simp only [gt_iff_lt, div_lt_div_iff i2 i1] at ie
  rw [deriv_div]
  apply div_neg_of_neg_of_pos; linarith
  apply pow_pos (Fp_pos ha (by linarith : c > 1))
  apply differentiable_Fp_a ha (by linarith : b > 0)
  apply differentiable_Fp_a ha (by linarith : c > 0)
  apply ne_of_gt (Fp_pos ha (by linarith))


lemma Lemma62_strictAntiOn (hr1 : 0 < r) (hr2 : r < Δ) : StrictAntiOn (fun i => Qp Δ i r) (Set.Iic 0) := by
  have i1 : ∀ x : ℝ, (2 : ℝ) ^ x > 0 := by
    simp only [gt_iff_lt, Nat.ofNat_pos, rpow_pos_of_pos, implies_true]
  have i2 : ∀ x ∈ Set.Ioi (0:ℝ), (2:ℝ) ^ x ∈ Set.Ioi 1 := by
    intro x hx
    apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hx
  apply strictAntiOn_of_deriv_neg (convex_Iic (0:ℝ))
  have : ContinuousOn (fun i ↦ Qp Δ i r) (Set.Iic 0) := by
    unfold Qp; apply ContinuousOn.div
    apply DifferentiableOn.continuousOn (Differentiable.differentiableOn differentiable_Ep_i)
    apply DifferentiableOn.continuousOn (Differentiable.differentiableOn differentiable_Ep_i)
    intro x _; apply ne_of_gt (Ep_r_pos (by linarith))
  exact this
  intro x hx; simp only [Set.nonempty_Ioi, interior_Iic'] at hx
  have : Set.EqOn (fun i ↦ Qp Δ i r) ((fun a => Fp (2^r) a / Fp (2^Δ) a) ∘ (fun i=> 2^i)) (Set.Iio 0) := by
    intro i _; simp only [Qp_of_Fp (by linarith)]
  rw [deriv_EqOn_Iio this hx, deriv_comp]
  apply mul_neg_of_neg_of_pos
  apply deriv_Fp_div_pos (i1 x) (i2 r hr1)
  apply rpow_lt_rpow_of_exponent_lt (by simp only [Nat.one_lt_ofNat]) hr2
  get_deriv (fun i ↦ 2 ^ i)
  simp only [List.Forall, toFun, gt_iff_lt, Nat.ofNat_pos, id_eq, implies_true]
  simp only [toFun, zero_mul, one_mul, zero_add] at h
  simp only [h, Nat.ofNat_pos, rpow_pos_of_pos, mul_pos_iff_of_pos_left, Nat.one_lt_ofNat, log_pos]
  apply DifferentiableAt.div
  apply differentiable_Fp_a (i1 x) (i1 r)
  apply differentiable_Fp_a (i1 x) (i1 Δ)
  apply ne_of_gt (Fp_pos (i1 x) (i2 Δ (by simp only [Set.mem_Ioi]; linarith)))
  apply DifferentiableAt.rpow <;> simp

lemma Lemma62 (hr1 : 0 ≤ r) (hr2 : r < Δ) : AntitoneOn (fun i => Qp Δ i r) (Set.Iic 0) := by
  cases le_iff_lt_or_eq.mp hr1 with
  | inl hr =>
    apply StrictAntiOn.antitoneOn
    exact Lemma62_strictAntiOn hr hr2
  | inr hr =>
    simp only [← hr, Qp, Ep_eq_zero, zero_div]
    exact antitoneOn_const
