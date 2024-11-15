import LNS.Tactic
import LNS.Definitions
import LNS.BasicErrTaylor

namespace LNS

noncomputable section

open Real

attribute [simp] rpow_pos_of_pos
attribute [simp] log_pos

def Fp b a := -(a + 1) * log (a + 1) + (a + 1) * log (a + b) - log b

def Fm b a := (1 - a) * log (1 - a) - (1 - a) * log (b - a) + log b

def U (x:ℝ) := 1 / x + log x - 1

def V (x:ℝ) := 2 * log (x + 1) - log x - 2 * log 2

def A (y:ℝ) := -2 * y * (log (y + 1) - log y - log 2) - y + 1

def B (y:ℝ) := y * (2 * log (y + 1) - log y - 2 * log 2)

def C (y:ℝ) := -2 * y / (y + 1) + 2 * log y - 2 * log (y + 1) + 2 * log 2 + 1

def Vm (x:ℝ) := 2 * log x - log (2 * x - 1)

def Am (y:ℝ) := 2 * y * log y - 2 * y * log (2 * y - 1) + 2 * y - 2

def Bm (y:ℝ) := y * (Vm y)

def Cm (y:ℝ) := 2 * log y - 2 * log (2 * y - 1) + 2 - 2 / y

/-
  Basic properties of the error correction functions
-/

private lemma aux_eq2 : (2:ℝ) ^ ((x:ℝ) - r) = 2^x / 2^r := by
  simp only [Nat.ofNat_pos, rpow_sub]

private lemma aux_eq3 : log (1 + 2 ^ (i:ℝ) / 2 ^ r) = log (2^i + 2^r) - r * log 2 := by
  have : (2:ℝ) ^ i > 0 := by simp
  have : (2:ℝ) ^ r > 0 := by simp
  have : 1 + (2:ℝ) ^ (i:ℝ) / 2 ^ r = (2^i + 2^r)  / 2 ^ r := by field_simp; ring_nf
  rw [this, log_div, log_rpow]; simp only [Nat.ofNat_pos]
  linarith; linarith

private lemma aux_eq4 (hi : i < 0) (hr : 0 ≤ r) :
    log (1 - 2 ^ (i:ℝ) / 2 ^ r) = log (2^r - 2^i) - r * log 2 := by
  have : (2:ℝ) ^ i > 0 := by simp
  have : (2:ℝ) ^ r > 0 := by simp
  have : 1 - (2:ℝ) ^ (i:ℝ) / 2 ^ r = (2^r - 2^i)  / 2 ^ r := by field_simp
  rw [this, log_div, log_rpow]; simp only [Nat.ofNat_pos]
  have : (2:ℝ) ^ i < 1 := by apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) hi
  have : (2:ℝ) ^ r ≥ 1 := by apply one_le_rpow (by norm_num) hr
  linarith; linarith

lemma U_pos (hx : 1 < x) : 0 < U x := by
  have eq : U 1 = 0 := by norm_num [U]
  rw [← eq]
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) _ _ (le_refl 1) (le_of_lt hx) hx
  · have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by simp only [Set.mem_Ici, ne_eq]; intros; linarith
    unfold U; fun_prop (disch := assumption)
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
  intro x hx; unfold U
  get_deriv (fun {X} ↦ 1 / X + log X - 1) at x
  simp only [List.Forall, toFun, ne_eq, id_eq, and_self]; linarith
  simp only [toFun] at h
  rw [HasDerivAt.deriv h]
  field_simp; apply lt_of_sub_pos; rw [(by ring: x ^ 2 - x = x*(x-1))]
  apply mul_pos (by linarith) (by linarith)

lemma deriv_Fp_a (hb : 0 < b) :
    Set.EqOn (deriv (Fp b)) (fun a => (a+1)/(a+b) - 1 - log (a+1) + log (a+b)) (Set.Ioi 0) := by
  unfold Fp
  get_deriv (fun a ↦ -(a + 1) * log (a + 1) + (a + 1) * log (a + b) - log b) within (Set.Ioi 0)
  simp only [Set.mem_Ioi, List.Forall, toFun, ne_eq, id_eq, and_imp]
  intro x hx
  constructor; linarith; constructor; linarith; linarith
  simp only [toFun] at h
  intro a ha
  rw [h.right a ha]
  have : a + 1 ≠ 0 := by simp only [Set.mem_Ioi] at ha; linarith
  field_simp; ring_nf

lemma differentiable_Fp_a (ha : 0 < a) (hb : 0 < b) : DifferentiableAt ℝ (Fp b) a := by
  unfold Fp; fun_prop (disch := linarith)

lemma deriv_Fp_b (ha : 0 < a) (hb : 0 < b) :
    deriv (fun b ↦ Fp b a) b = a * (b - 1) / (b * (a + b)) := by
  unfold Fp
  get_deriv (fun b ↦ -(a + 1) * log (a + 1) + (a + 1) * log (a + b) - log b) within (Set.Ioi 0)
  simp only [Set.mem_Ioi, List.Forall, toFun, ne_eq, id_eq]
  intro x hx; split_ands <;> linarith
  simp only [toFun] at h
  rw [ h.right b hb]
  have : a + b ≠ 0 := by linarith
  field_simp; ring_nf

lemma differentiable_Fp_b (ha : 0 < a) (hb : 0 < b) : DifferentiableAt ℝ (fun b ↦ Fp b a) b := by
  unfold Fp; fun_prop (disch := linarith)

lemma deriv_Fp_a_b (ha : 0 < a) (hb : 0 < b) :
    deriv (fun b ↦ deriv (Fp b) a) b = (b - 1) / (a + b) ^ 2 := by
  have e: Set.EqOn (fun b ↦ deriv (Fp b) a) (fun b => (a+1)/(a+b) - 1 - log (a+1) + log (a+b)) (Set.Ioi 0) := by
    unfold Set.EqOn; intro x hx; simp only
    rw [deriv_Fp_a hx ha]
  rw [deriv_EqOn_Ioi e hb]
  get_deriv (fun b ↦ (a + 1) / (a + b) - 1 - log (a + 1) + log (a + b)) within (Set.Ioi 0)
  simp only [Set.mem_Ioi, List.Forall, toFun, ne_eq, id_eq]
  intro x hx; split_ands <;> linarith
  simp only [toFun] at h
  rw [h.right b hb]
  have : a + 1 ≠ 0 := by linarith
  have : a + b ≠ 0 := by linarith
  field_simp; ring_nf

lemma differentiable_Fp_a_b (ha : 0 < a) (hb : 0 < b) :
    DifferentiableAt ℝ (fun b ↦ deriv (Fp b) a) b := by
  have e: Set.EqOn (fun b ↦ deriv (Fp b) a) (fun b => (a+1)/(a+b) - 1 - log (a+1) + log (a+b)) (Set.Ioi 0) := by
    unfold Set.EqOn; intro x hx; simp only
    rw [deriv_Fp_a hx ha]
  get_deriv (fun b ↦ (a + 1) / (a + b) - 1 - log (a + 1) + log (a + b)) within (Set.Ioi 0)
  simp only [Set.mem_Ioi, List.Forall, toFun, ne_eq, id_eq]
  intro x hx; split_ands <;> linarith
  simp only [toFun] at h
  apply DifferentiableOn.differentiableAt (DifferentiableOn.congr h.left e)
  apply Ioi_mem_nhds hb

lemma deriv_Fp_a_pos (ha : 0 < a) (hb : 1 < b) : 0 < deriv (Fp b) a := by
  have e1 : deriv (Fp b) a = (fun b ↦ deriv (Fp b) a) b := by simp only
  have : a + 1 ≠ 0 := by linarith
  have e2 : (fun b ↦ deriv (Fp b) a) 1 = 0 := by
    simp only [@deriv_Fp_a 1 (by norm_num) a ha, sub_add_cancel]
    field_simp
  rw [e1, ← e2]
  have e: Set.EqOn (fun b ↦ deriv (Fp b) a) (fun b => (a+1)/(a+b) - 1 - log (a+1) + log (a+b)) (Set.Ici 1) := by
    unfold Set.EqOn; intro x hx; simp only
    simp only [Set.mem_Ici] at hx
    rw [deriv_Fp_a (by linarith : x > 0) ha]
  have: StrictMonoOn (fun b ↦ deriv (Fp b) a) (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    apply ContinuousOn.congr _ e
    have : ∀ x ∈ Set.Ici 1, a + x ≠ 0 := by intro x hx; simp only [Set.mem_Ici] at hx; linarith
    fun_prop (disch := assumption)
    intro x hx; simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
    rw [deriv_Fp_a_b ha (by linarith)]
    have : x - 1 >0 := by linarith
    have : a + x > 0 := by linarith
    positivity
  apply this (by simp only [Set.mem_Ici, le_refl]) (by simp only [Set.mem_Ici]; linarith) hb

lemma Fp_pos (ha: 0 < a) (hb: 1 < b) : 0 < (Fp b) a := by
  have e1 : (Fp b) a = (fun b ↦ (Fp b) a) b := by simp only
  have e2 : (fun b ↦  (Fp b) a) 1 = 0 := by simp only [Fp, neg_add_rev, log_one, sub_zero]; ring_nf
  rw [e1, ← e2]
  have: StrictMonoOn (fun b ↦ (Fp b) a) (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    unfold Fp
    have : ∀ x ∈ Set.Ici 1, a + x ≠ 0 := by intro x hx; simp only [Set.mem_Ici] at hx; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by intro x hx; simp only [Set.mem_Ici] at hx; linarith
    fun_prop (disch := assumption)
    intro x hx
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
    rw [deriv_Fp_b ha (by linarith)]
    have : x - 1 > 0 := by linarith
    have : a + x > 0 := by linarith
    positivity
  apply this (by simp only [Set.mem_Ici, le_refl]) (by simp only [Set.mem_Ici]; linarith) hb

lemma Qp_of_Fp (hΔ : 0 < Δ) : Qp Δ i r = ((fun a => Fp (2 ^ r) a / Fp (2 ^ Δ) a) ∘ (fun i=> 2 ^ i)) i := by
  unfold Qp
  have : Fp (2 ^ Δ) (2 ^ i) > 0 := by
    apply Fp_pos; norm_num
    apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) (by linarith)
  have : Ep i Δ > 0 := by apply Ep_r_pos (by linarith)
  field_simp
  unfold Fp Ep ; simp only [deriv_Φp, neg_add_rev, Φp, logb]
  field_simp
  simp only [aux_eq2, aux_eq3, Nat.ofNat_pos, log_rpow]
  ring_nf

lemma deriv_Fm_a (hb : 1 ≤ b) :
    Set.EqOn (deriv (Fm b)) (fun a => (1 - a) / (b - a) - 1 - log (1 - a) + log (b-a)) (Set.Ioo 0 1) := by
  unfold Fm
  get_deriv (fun a ↦ (1 - a) * log (1 - a) - (1 - a) * log (b - a) + log b) within (Set.Ioo 0 1)
  simp only [Set.mem_Ioc, List.Forall, toFun, ne_eq, id_eq, and_imp]
  intro x hx; simp only [Set.mem_Ioo] at hx
  constructor; linarith; constructor; linarith; linarith
  simp only [toFun] at h
  intro a ha
  rw [h.right a ha]
  have : 1 - a ≠ 0 := by simp only [Set.mem_Ioo] at ha; linarith
  have : b - a ≠ 0 := by simp only [Set.mem_Ioo] at ha; linarith
  field_simp; ring_nf

lemma differentiable_Fm_a (ha : a ∈ Set.Ioo 0 1) (hb : 1 ≤ b) : DifferentiableAt ℝ (Fm b) a := by
  unfold Fm; simp only [Set.mem_Ioo] at ha
  fun_prop (disch := linarith)

lemma deriv_Fm_b (ha : a ∈ Set.Ioo 0 1) (hb : 1 ≤ b) : deriv (fun b ↦ Fm b a) b = a * (b - 1) / (b * (b - a)) := by
  unfold Fm
  simp only [Set.mem_Ioo] at ha hb
  get_deriv (fun b ↦ (1 - a) * log (1 - a) - (1 - a) * log (b - a) + log b) within (Set.Ici 1)
  simp only [Set.mem_Ici, List.Forall, toFun, ne_eq, id_eq]
  intro x hx; split_ands <;> linarith
  simp only [toFun] at h
  rw [h.right b hb]
  have : b - a ≠ 0 := by linarith
  field_simp; ring_nf

lemma differentiable_Fm_b (ha : a ∈ Set.Ioo 0 1) (hb : 1 ≤ b) : DifferentiableAt ℝ (fun b ↦ Fm b a) b := by
  unfold Fm; simp only [Set.mem_Ioo] at ha
  fun_prop (disch := linarith)

lemma deriv_Fm_a_b (ha : a ∈ Set.Ioo 0 1) (hb : 1 < b) :
     deriv (fun b ↦ deriv (Fm b) a) b = (b - 1) / (b - a) ^ 2 := by
  have e: Set.EqOn (fun b ↦ deriv (Fm b) a) (fun b => (1-a)/(b-a) - 1 - log (1-a) + log (b-a)) (Set.Ioi 1) := by
    unfold Set.EqOn; intro x hx; simp only
    rw [deriv_Fm_a _ ha]
    exact le_of_lt hx
  rw [deriv_EqOn_Ioi e hb]
  get_deriv (fun b ↦ (1 - a) / (b - a) - 1 - log (1 - a) + log (b - a)) within (Set.Ioi 1)
  simp only [Set.mem_Ioi, List.Forall, toFun, ne_eq, id_eq]
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  intro x hx; split_ands <;> linarith
  simp only [toFun] at h
  rw [h.right b hb]
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  have : 1 - a ≠ 0 := by linarith
  have : b - a ≠ 0 := by linarith
  field_simp; ring_nf

lemma differentiable_Fm_a_b (ha : a ∈ Set.Ioo 0 1) (hb : 1 < b) :
    DifferentiableAt ℝ (fun b ↦ deriv (Fm b) a) b := by
  have e: Set.EqOn (fun b ↦ deriv (Fm b) a) (fun b => (1-a)/(b-a) - 1 - log (1-a) + log (b-a))  (Set.Ioi 1) := by
    unfold Set.EqOn; intro x hx; simp only
    rw [deriv_Fm_a _ ha]
    simp_all only [Set.mem_Ioo, Set.mem_Ioi, Set.mem_Ici]; linarith
  get_deriv (fun b => (1-a)/(b-a) - 1 - log (1-a) + log (b-a)) within (Set.Ioi 1)
  simp only [Set.mem_Ioi, List.Forall, toFun, ne_eq, id_eq]
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  intro x hx; split_ands <;> linarith
  simp only [toFun] at h
  apply DifferentiableOn.differentiableAt (DifferentiableOn.congr h.left e)
  apply Ioi_mem_nhds hb

lemma deriv_Fm_a_pos (ha : a ∈ Set.Ioo 0 1) (hb : 1 < b) : 0 < deriv (Fm b) a := by
  have e1 : deriv (Fm b) a = (fun b ↦ deriv (Fm b) a) b := by simp only
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  have : 1 - a ≠ 0 := by linarith
  have e2 : (fun b ↦ deriv (Fm b) a) 1 = 0 := by
    simp only [@deriv_Fm_a 1 (by simp only [Set.mem_Ici, le_refl]) a ha]
    field_simp
  rw [e1,← e2]
  have e : Set.EqOn (fun b ↦ deriv (Fm b) a) (fun b => (1-a)/(b-a) - 1 - log (1-a) + log (b-a))  (Set.Ici 1) := by
    unfold Set.EqOn; intro x hx; simp only
    rw [deriv_Fm_a hx ha]
  have : StrictMonoOn (fun b ↦ deriv (Fm b) a) (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    apply ContinuousOn.congr _ e
    have : ∀ x ∈ Set.Ici 1, x - a ≠ 0 := by intro x hx; simp only [Set.mem_Ici] at hx; linarith
    fun_prop (disch := assumption)
    intro x hx; simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
    rw [deriv_Fm_a_b ha hx]
    have : x - 1 >0 := by linarith
    have : x - a > 0 := by linarith
    positivity
  apply this (by simp only [Set.mem_Ici, le_refl]) (by simp only [Set.mem_Ici]; linarith) hb

lemma Fm_pos (ha : a ∈ Set.Ioo 0 1) (hb : 1 < b) : 0 < (Fm b) a := by
  have e1 : (Fm b) a = (fun b ↦ (Fm b) a) b := by simp only
  have e2 : (fun b ↦  (Fm b) a) 1 = 0 := by simp only [Fm, neg_add_rev, log_one, sub_zero]; ring_nf
  rw [e1, ← e2]
  simp only [Set.mem_Ioo, Set.mem_Ioi] at ha hb
  have: StrictMonoOn (fun b ↦ (Fm b) a) (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    unfold Fm
    have : ∀ x ∈ Set.Ici 1, x - a ≠ 0 := by intro x hx; simp only [Set.mem_Ici] at hx; linarith
    have : ∀ x ∈ Set.Ici (1:ℝ) , x ≠ 0 := by intro x hx; simp only [Set.mem_Ici] at hx; linarith
    fun_prop (disch := assumption)
    intro x hx
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
    rw [deriv_Fm_b ha (le_of_lt hx)]
    have : x - 1 > 0 := by linarith
    have : x - a > 0 := by linarith
    have : a > 0 := by linarith
    positivity
  apply this (by simp only [Set.mem_Ici, le_refl]) (by simp only [Set.mem_Ici]; linarith) hb

lemma Qm_of_Fm (hi : i ∈ Set.Iio 0) (hr : 0 ≤ r) (hΔ : 0 < Δ) :
    Qm Δ i r = ((fun a => Fm (2 ^ r) a / Fm (2 ^ Δ) a) ∘ (fun i => 2 ^ i)) i := by
  unfold Qm; simp only [Function.comp_apply]
  have : 1 - (2:ℝ)^i > 0 := by
    simp only [gt_iff_lt, sub_pos]
    apply rpow_lt_one_of_one_lt_of_neg (by simp only [Nat.one_lt_ofNat]) hi
  have : Fm (2 ^ Δ) (2 ^ i) > 0 := by
    apply Fm_pos; norm_num; linarith
    apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) (by linarith)
  have : Em i Δ > 0 := by apply Em_r_pos hi hΔ
  field_simp
  simp only [Set.mem_Iio] at hi
  unfold Fm Em ; simp only [deriv_Φm hi, neg_add_rev, Φm, logb]
  simp only [aux_eq2, aux_eq4 hi hr, aux_eq4 hi (le_of_lt hΔ), Nat.ofNat_pos, log_rpow]
  field_simp; ring_nf
