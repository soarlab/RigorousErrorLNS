import LNS.Common
import LNS.Tactic
import LNS.Basic
import Mathlib.Analysis.Calculus.LHopital
open LNS

open Real

open Real Filter Topology

noncomputable section

lemma Qp_hi_denom_valid (hΔ : Δ > 0) : 2 ^ (-Δ) + Δ * log 2 - 1 ≠ 0 := by
  have: (2:ℝ)^Δ > 1 :=by apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hΔ
  have h:= U_pos this; rw[U,log_rpow, one_div, ← rpow_neg] at h;
  any_goals linarith

lemma deriv_Fp_tendsto (hr : r ≥ 0) :
    Tendsto (deriv (Fp (2 ^ r))) (𝓝[>] 0) (𝓝 (2 ^ (-r) + r * log 2 - 1)) := by
  have: (2:ℝ) ^ r ≥ 1:=by apply one_le_rpow (by simp only [Nat.one_le_ofNat]) hr
  have: deriv (Fp (2 ^ r)) =ᶠ[(𝓝[>] 0)] (fun a => (a+1)/(a+2 ^ r) - 1 - log (a+1) + log (a+2 ^ r)) := by
    apply Filter.eventuallyEq_of_mem self_mem_nhdsWithin (deriv_Fp_a _)
    linarith
  rw[Filter.tendsto_congr' this]
  have: 2 ^ (-r) + r * log 2 - 1 = (fun a ↦ (a + 1) / (a + 2 ^ r) - 1 - log (a + 1) + log (a + 2 ^ r)) 0 :=by
    simp only [zero_add, one_div, log_one, sub_zero];
    rw[log_rpow, rpow_neg];
    ring_nf; simp only [Nat.ofNat_nonneg]; simp only [Nat.ofNat_pos]
  rw[this]
  apply ContinuousWithinAt.tendsto
  apply ContinuousAt.continuousWithinAt
  fun_prop(disch:=linarith)

lemma deriv_Fm_tendsto (hr : r ≥ 0) :
    Tendsto (deriv (Fm (2 ^ r))) (𝓝[>] 0) (𝓝 (2 ^ (-r) + r * log 2 - 1)) := by
  have: (2:ℝ) ^ r ≥ 1:=by apply one_le_rpow (by simp only [Nat.one_le_ofNat]) hr
  have: deriv (Fm (2 ^ r)) =ᶠ[(𝓝[>] 0)] (fun a => (1-a)/(2 ^ r-a) - 1 - log (1-a) + log (2 ^ r-a)) := by
    apply Filter.eventuallyEq_of_mem _ (deriv_Fm_a this)
    exact Ioo_mem_nhdsWithin_Ioi' (by norm_num)
  rw[Filter.tendsto_congr' this]
  have: 2 ^ (-r) + r * log 2 - 1 = (fun a => (1-a)/(2 ^ r-a) - 1 - log (1-a) + log (2 ^ r-a)) 0 :=by
    simp only [zero_add, one_div, log_one, sub_zero];
    rw[log_rpow, rpow_neg];
    ring_nf; simp only [Nat.ofNat_nonneg]; simp only [Nat.ofNat_pos]
  rw[this]
  apply ContinuousWithinAt.tendsto
  apply ContinuousAt.continuousWithinAt
  fun_prop(disch:=linarith)

lemma Fp_tendsto (hr : r ≥ (0:ℝ)) :  Tendsto (Fp (2 ^ r)) (𝓝[>] 0) (𝓝 0) := by
  have: (2:ℝ) ^ r ≥ 1:= by apply one_le_rpow (by norm_num) hr
  have: 0 = Fp (2 ^ r) 0 := by simp only [Fp, zero_add, log_one, mul_zero, one_mul, sub_self]
  nth_rewrite 3 [this]
  apply ContinuousWithinAt.tendsto
  apply ContinuousAt.continuousWithinAt
  unfold Fp
  fun_prop(disch:=linarith)

lemma Fm_tendsto (hr : r ≥ (0:ℝ)) : Tendsto (Fm (2 ^ r)) (𝓝[>] 0) (𝓝 0) := by
  have: (2:ℝ) ^ r ≥ 1:=by apply one_le_rpow (by norm_num) hr
  have: 0 = Fm (2 ^ r) 0 :=by simp only [Fm, sub_zero, log_one, mul_zero, one_mul, zero_sub,neg_add_cancel]
  nth_rewrite 3 [this]
  apply ContinuousWithinAt.tendsto
  apply ContinuousAt.continuousWithinAt
  unfold Fm
  fun_prop(disch:=linarith)


lemma Lemma61 (hr : r ≥ 0) (hΔ : Δ > 0): Tendsto (fun i => Qp Δ i r) atBot (𝓝 (Qp_hi Δ r)) := by
  have t1: Tendsto (fun a ↦ Fp (2^r) a / Fp (2^Δ) a) (𝓝[>] (0:ℝ)) (𝓝 (Qp_hi Δ r)) := by
    have h1: DifferentiableOn ℝ (Fp (2 ^ r)) (Set.Ioo 0 1) := by
      intro a ha
      apply DifferentiableAt.differentiableWithinAt (differentiable_Fp_a ha.1 _)
      apply rpow_pos_of_pos (by norm_num) r
    have h2: ∀ x ∈ Set.Ioo 0 1, deriv (Fp (2 ^ Δ)) x ≠ 0 :=by
      intro x hx
      apply ne_of_gt (deriv_Fp_a_pos hx.1 _)
      apply one_lt_rpow (by simp only [Nat.one_lt_ofNat]) hΔ
    apply deriv.lhopital_zero_right_on_Ioo zero_lt_one h1 h2 (Fp_tendsto hr) (Fp_tendsto (le_of_lt hΔ))
    unfold Qp_hi;
    apply Tendsto.div (deriv_Fp_tendsto hr) (deriv_Fp_tendsto (le_of_lt hΔ)) (Qp_hi_denom_valid hΔ)
  have t21: Tendsto (fun (i:ℝ) ↦ 2 ^ i) atBot (𝓝 (0:ℝ)):=by
    apply tendsto_rpow_atBot_of_base_gt_one ; simp only [Nat.one_lt_ofNat]
  have t2: Tendsto (fun (i:ℝ) ↦ 2 ^ i) atBot (𝓝[>] (0:ℝ)):=by
    apply tendsto_nhdsWithin_iff.mpr
    simp only [t21, Set.mem_Ioi, Nat.ofNat_pos, rpow_pos_of_pos, eventually_atBot, implies_true,
      exists_const, and_self]
  have :(fun i => Qp Δ i r) = (fun a ↦ Fp (2^r) a / Fp (2^Δ) a) ∘ (fun i=> 2^i):= by ext x; rw[Qp_of_Fp hΔ]
  rw[this]
  apply Tendsto.comp t1 t2;

lemma Lemma61m (hr : r ≥ 0) (hΔ : Δ > 0) : Tendsto (fun i => Qm Δ i r) atBot (𝓝 (Qm_lo Δ r)) := by
  have t1: Tendsto (fun a ↦ Fm (2^r) a / Fm (2^Δ) a) (𝓝[>] (0:ℝ)) (𝓝 (Qp_hi Δ r)) := by
    have h1: DifferentiableOn ℝ (Fm (2 ^ r)) (Set.Ioo 0 1) := by
      intro a ha
      apply DifferentiableAt.differentiableWithinAt (differentiable_Fm_a ha _)
      exact one_le_rpow (by norm_num) hr
    have h2: ∀ x ∈ Set.Ioo 0 1, deriv (Fm (2 ^ Δ)) x ≠ 0 :=by
      intro x hx
      apply ne_of_gt (deriv_Fm_a_pos hx _)
      exact one_lt_rpow (by norm_num) hΔ
    apply deriv.lhopital_zero_right_on_Ioo zero_lt_one h1 h2 (Fm_tendsto hr) (Fm_tendsto (le_of_lt hΔ))
    unfold Qp_hi;
    apply Tendsto.div (deriv_Fm_tendsto hr) (deriv_Fm_tendsto (le_of_lt hΔ)) (Qp_hi_denom_valid hΔ)
  have t21: Tendsto (fun (i:ℝ) ↦ 2 ^ i) atBot (𝓝 (0:ℝ)):=by
    apply tendsto_rpow_atBot_of_base_gt_one ; simp only [Nat.one_lt_ofNat]
  have t2: Tendsto (fun (i:ℝ) ↦ 2 ^ i) atBot (𝓝[>] (0:ℝ)):=by
    apply tendsto_nhdsWithin_iff.mpr
    simp only [t21, Set.mem_Ioi, Nat.ofNat_pos, rpow_pos_of_pos, eventually_atBot, implies_true,
      exists_const, and_self]
  have : (fun i => Qm Δ i r) =ᶠ[(atBot)] (fun a ↦ Fm (2^r) a / Fm (2^Δ) a) ∘ (fun i=> 2^i):= by
    have: Set.EqOn (fun i => Qm Δ i r) ((fun a ↦ Fm (2^r) a / Fm (2^Δ) a) ∘ (fun i=> 2^i)) (Set.Iio 0) :=by
      intro i hi;
      simp only [Qm_of_Fm hi hr hΔ, Function.comp_apply];
    apply Filter.eventuallyEq_of_mem _ this
    exact (Filter.Iio_mem_atBot (0:ℝ))
  rw[Filter.tendsto_congr' this]
  apply Tendsto.comp t1 t2;
