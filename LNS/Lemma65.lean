import LNS.Common
import LNS.Tactic
import LNS.Basic
set_option maxHeartbeats 10000000

open LNS

open Real

noncomputable section

private def Gm a b := Fm b a / deriv (Fm b) a

private def Km a b := -a * a * log (1-a) + a * a * log (b-a) + a * b - a + b * log (1-a) + b * log b - b * log (b-a)

lemma deriv_Km (ha: a ∈ (Set.Ioo 0 1)): Set.EqOn (deriv (Km a))
      (fun b=> (a*a)/(b-a) + a - b/(b-a) + log b + log (1-a) - log (b-a) + (1:ℝ)) (Set.Ici 1) := by
  unfold Km
  get_deriv (fun b ↦ -a * a * log (1 - a) + a * a * log (b - a) + a * b - a + b * log (1 - a) + b * log b - b * log (b - a))
      within (Set.Ici 1)
  simp only [Set.mem_Ici, List.Forall, toFun, ne_eq, id_eq]
  simp only [Set.mem_Ioo] at ha
  intro x hx; split_ands <;> linarith
  simp only [toFun] at h
  intro b hb
  rw [h.right b hb]
  simp only [Set.mem_Ioo, Set.mem_Ici] at ha hb
  field_simp; ring_nf

lemma deriv2_Km (ha: a ∈ (Set.Ioo 0 1)):  Set.EqOn (deriv (deriv (Km a)))
      (fun b=> -((a^2*(b-1))/(b*(b-a)^2))) (Set.Ioi 1) := by
  have e : Set.EqOn (deriv (Km a))
      (fun b=> (a*a)/(b-a) + a - b/(b-a) + log b + log (1-a) - log (b-a) + (1:ℝ)) (Set.Ioi 1) := by
    apply Set.EqOn.mono _ (deriv_Km ha)
    simp only [Set.Ioi_subset_Ici_iff, le_refl]
  intro b hb; rw [deriv_EqOn_Ioi e hb]
  get_deriv (fun b=> (a*a)/(b-a) + a - b/(b-a) + log b + log (1-a) - log (b-a) + (1:ℝ)) within (Set.Ioi 1)
  simp only [Set.mem_Ioi, List.Forall, toFun, ne_eq, id_eq, and_self_left]
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  intro x hx; split_ands <;> linarith
  simp only [toFun] at h
  rw [h.right b hb]
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  have : b - a ≠ 0 := by linarith
  field_simp; ring_nf

lemma deriv_Km_strictAnti (ha: a ∈ (Set.Ioo 0 1)): StrictAntiOn (deriv (Km a)) (Set.Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1)
  apply ContinuousOn.congr _ (deriv_Km ha)
  have : ∀ x ∈ Set.Ici 1, a + x ≠ 0 := by
    simp only [Set.mem_Ici, ne_eq]; simp only [Set.mem_Ioo] at ha
    intro x hx; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ), x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intro x hx; linarith
  have : ∀ x ∈ Set.Ici 1, x - a ≠ 0 := by intro x hx; simp only [Set.mem_Ici, Set.mem_Ioo] at hx ha; linarith
  fun_prop (disch := assumption)
  intro b hb; simp only [Set.nonempty_Iio, interior_Ici'] at hb
  simp only [deriv2_Km ha hb]
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  have :  a * a * (1 - b) / (b * (a + b) ^ 2) =  - (a * a * (b-1) / (b * (a + b) ^ 2)) := by ring_nf
  simp only [this, Left.neg_neg_iff, gt_iff_lt]
  have : b - 1 > 0 := by linarith
  have : a > 0 := ha.left
  have : b - a > 0 := by linarith
  positivity

lemma deriv_Km_neg (ha: a ∈ (Set.Ioo 0 1)) (hb: b ∈ (Set.Ioi 1)) : deriv (Km a) b < 0 := by
  simp only [Set.mem_Ioi] at hb
  have :  deriv (Km a) 1 = 0 := by
    rw [deriv_Km ha (by simp only [Set.mem_Ici, le_refl])]
    simp only [Set.mem_Ioo] at ha
    have : b - a > 0 := by linarith
    have : 1 - a > 0 := by linarith
    field_simp; ring_nf
  rw [← this]
  apply (deriv_Km_strictAnti ha) (by simp only [Set.mem_Ici, le_refl]) (by simp only [Set.mem_Ici]; linarith) hb


lemma Km_strictAnti (ha: a ∈ (Set.Ioo 0 1)): StrictAntiOn (Km a) (Set.Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1)
  unfold Km
  have : ∀ x ∈ Set.Ici 1, x - a ≠ 0 := by
    simp only [Set.mem_Ici, ne_eq]; simp only [Set.mem_Ioo] at ha
    intro x hx; linarith
  have : ∀ x ∈ Set.Ici (1:ℝ), x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intro x hx; linarith
  fun_prop (disch := assumption)
  intro b hb
  apply deriv_Km_neg ha; simp only [Set.nonempty_Iio, interior_Ici'] at hb; exact hb


lemma Km_neg (ha: a ∈ (Set.Ioo 0 1)) (hb: b ∈ (Set.Ioi 1)) : Km a b < 0 := by
  have : Km a 1 = 0 := by simp only [Km, neg_mul, neg_add_cancel, mul_one, zero_add, sub_self,
    one_mul, log_one, mul_zero, add_zero]
  rw [← this]; simp only [Set.mem_Ioi] at hb
  apply (Km_strictAnti ha) (by simp only [Set.mem_Ici, le_refl]) _ hb
  simp only [Set.mem_Ici]; linarith


lemma deriv_Gm_b_pos (ha: a ∈ (Set.Ioo 0 1)) (hb: b ∈ (Set.Ioi 1))
    : (deriv (Gm a)) b > 0 := by
  unfold Gm
  simp only [Set.mem_Ioc, Set.mem_Ioi] at ha hb
  rw [deriv_div]
  have : deriv (Fm b) a ^ 2 > 0 := by apply pow_pos (deriv_Fm_a_pos ha hb)
  apply div_pos
  rw [deriv_Fm_a_b ha hb, deriv_Fm_b ha (le_of_lt hb), deriv_Fm_a (le_of_lt hb) ha]
  unfold Fm
  simp only
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  have : b - a > 0 := by linarith
  have : a * (b - 1) / (b * (b - a)) * ((1 - a) / (b - a) - 1 - log (1 - a) + log (b - a)) -
    ((1 - a) * log (1 - a) - (1 - a) * log (b - a) + log b) * ((b - 1) / (b - a) ^ 2)
    = -((b-1)/(b*(b-a)^2)* (Km a b)) := by
    unfold Km; field_simp; ring_nf
  rw [this]; simp only [Left.neg_pos_iff, gt_iff_lt]; apply mul_neg_of_pos_of_neg
  have : b - 1 > 0 := by linarith
  have : b - a > 0 := by linarith
  positivity
  apply Km_neg ha hb
  apply pow_pos (deriv_Fm_a_pos ha hb)
  exact differentiable_Fm_b ha (le_of_lt hb)
  exact differentiable_Fm_a_b ha hb
  apply ne_of_gt (deriv_Fm_a_pos ha hb)

lemma Mono_Gm_b (ha: a ∈ (Set.Ioo 0 1)) : StrictMonoOn (Gm a) (Set.Ioi 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 1)
  unfold Gm
  apply ContinuousOn.div
  apply ContinuousAt.continuousOn
  intro b hb
  apply DifferentiableAt.continuousAt (differentiable_Fm_b ha (le_of_lt hb))
  apply ContinuousAt.continuousOn
  intro b hb
  apply DifferentiableAt.continuousAt (differentiable_Fm_a_b ha hb)
  intro b hb; apply ne_of_gt (deriv_Fm_a_pos ha hb)
  intro b hb; simp only [interior_Ioi, Set.mem_Ioi] at hb; exact deriv_Gm_b_pos ha hb

lemma deriv_Fm_div_pos (ha: a ∈ (Set.Ioo 0 1)) (hb: b > 1) (hc: c > b) : deriv (fun a ↦ Fm b a / Fm c a) a > 0 := by
  have ie : Gm a b < Gm a c := by apply Mono_Gm_b ha hb (by simp only [Set.mem_Ioi];linarith) hc
  unfold Gm at ie
  have i1 : deriv (Fm b) a > 0 := by apply deriv_Fm_a_pos ha hb
  have i2 : deriv (Fm c) a > 0 := by apply deriv_Fm_a_pos ha; linarith
  simp only [div_lt_div_iff i1 i2] at ie
  rw [deriv_div]
  apply div_pos; linarith
  apply pow_pos (Fm_pos ha (by linarith))
  apply differentiable_Fm_a ha (le_of_lt hb)
  apply differentiable_Fm_a ha (by linarith)
  apply ne_of_gt (Fm_pos ha (by linarith))


lemma Lemma65_strictMono (hr1 : 0 < r) (hr2 : r < Δ) :
    StrictMonoOn (fun i => Qm Δ i r) (Set.Iio 0) := by
  have i1 : ∀ x ∈ Set.Iio (0:ℝ), (2:ℝ) ^ x ∈ Set.Ioo 0 1 := by
    intro x hx
    simp only [Set.mem_Ioo, Nat.ofNat_pos, rpow_pos_of_pos, true_and]
    apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) hx
  have i2 : ∀ x ∈ Set.Ioi (0:ℝ), (2:ℝ) ^ x ∈ Set.Ioi 1 := by
    intro x hx
    apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hx
  apply strictMonoOn_of_deriv_pos (convex_Iio 0)
  have : ContinuousOn (fun i ↦ Qm Δ i r) (Set.Iio 0) := by
    have : ∀ t > 0, DifferentiableOn ℝ (Em_i t) (Set.Iio 0) := by
      intro t ht
      apply DifferentiableOn.mono (@differentiable_Em_i t (by simp only [Set.mem_Ici]; linarith))
      exact subset_refl _
    unfold Qm; apply ContinuousOn.div
    apply DifferentiableOn.continuousOn (this r hr1)
    apply DifferentiableOn.continuousOn (this Δ (by linarith))
    intro x hx; simp only [Set.mem_Iic] at hx
    apply ne_of_gt (Em_r_pos _ (by linarith))
    simp only [Set.mem_Iio] at hx; linarith
  exact this
  intro x hx; simp only [interior_Iio, Set.mem_Iio] at hx
  have : Set.EqOn (fun i ↦ Qm Δ i r) ((fun a => Fm (2^r) a / Fm (2^Δ) a) ∘ (fun i=> 2^i)) (Set.Iio 0) := by
    intro i hi; simp only [Function.comp_apply]; rw [Qm_of_Fm]; simp only [Function.comp_apply]
    simp only [Set.mem_Iio]; simp only [Set.mem_Iio] at hi; linarith; linarith; linarith
  rw [deriv_EqOn_Iio this hx, deriv.comp]
  apply mul_pos
  any_goals have hx : x ∈ Set.Iio 0 := by simp only [Set.mem_Iio] ; linarith
  apply deriv_Fm_div_pos (i1 x hx) (i2 r hr1)
  apply rpow_lt_rpow_of_exponent_lt (by simp only [Nat.one_lt_ofNat]) hr2
  get_deriv (fun i ↦ 2 ^ i)
  simp only [List.Forall, toFun, gt_iff_lt, Nat.ofNat_pos, id_eq, implies_true]
  simp only [toFun, zero_mul, one_mul, zero_add] at h
  simp only [h, Nat.ofNat_pos, rpow_pos_of_pos, mul_pos_iff_of_pos_left, Nat.one_lt_ofNat, log_pos]
  apply DifferentiableAt.div
  apply differentiable_Fm_a (i1 x hx) (le_of_lt (i2 r hr1))
  apply differentiable_Fm_a (i1 x hx) (le_of_lt (i2 Δ (by simp only [Set.mem_Ioi]; linarith)))
  apply ne_of_gt (Fm_pos (i1 x hx) (i2 Δ (by simp only [Set.mem_Ioi]; linarith)))
  apply DifferentiableAt.rpow <;> simp

lemma Lemma65 (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    MonotoneOn (fun i => Qm Δ i r) (Set.Iio 0) := by
  cases le_iff_lt_or_eq.mp hr1 with
  | inl hr =>
    apply StrictMonoOn.monotoneOn
    exact Lemma65_strictMono hr hr2
  | inr hr =>
    simp only [← hr, Qm, Em_eq_zero, zero_div]
    exact antitoneOn_const
