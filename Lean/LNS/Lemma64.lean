import LNS.Tactic
import LNS.Definitions
import LNS.Lemma63

namespace LNS

noncomputable section

open Real

private def Wp c Δ r t := (Ep c r - Ep c (r - t)) / Ep c Δ

private def Wtp c Δ t r := Wp c Δ r t

private lemma monoWp1 (hd : 0 < Δ) (h1 : ΔP ≤ r) (htp : t ≤ ΔP) :
    (Wp c Δ) r t ≤ (Wp c Δ) r ΔP := by
  have ep : Ep c Δ > 0 := by apply Ep_r_pos; linarith
  unfold Wp; rw [div_le_div_iff_of_pos_right ep]; apply sub_le_sub_left
  apply Ep_r_monotoneOn
  simp only [Set.mem_Ici, sub_nonneg]; linarith
  simp only [Set.mem_Ici, sub_nonneg]; linarith
  linarith

private lemma monoWp2 (hd : 0 < Δ) (ht : 0 ≤ t) (htr : t ≤ r) (htd : r ≤ Δ):
    (Wp c Δ) r t ≤  (Wp c Δ) Δ t := by
  have ep : Ep c Δ > 0 := by apply Ep_r_pos; linarith
  unfold Wp; rw [div_le_div_iff_of_pos_right ep]
  have ec2 : (fun y ↦ Ep c (y - t)) = (fun y => Ep c y) ∘ (fun y => y-t) := by ext y; simp only [Function.comp_apply]
  have diff : DifferentiableOn ℝ (fun x => Ep c x - Ep c (x - t)) (Set.Ici t) := by fun_prop
  have : MonotoneOn (fun x => Ep c x - Ep c (x - t)) (Set.Ici t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici t) (by fun_prop)
    apply DifferentiableOn.mono diff
    simp only [Set.nonempty_Iio, interior_Ici', Set.Ioi_subset_Ici_iff, le_refl]
    intro x hx
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
    rw [deriv_sub (by fun_prop) (by fun_prop), ec2, deriv_comp _ (by fun_prop) (by fun_prop)]
    simp only [differentiableAt_id', differentiableAt_const, deriv_sub, deriv_id'', deriv_const',
      sub_zero, mul_one, sub_nonneg]
    rw [(by simp only: (fun y ↦ Ep c y) = Ep c)]
    apply StrictMonoOn.monotoneOn deriv_Ep_r_strictMono
    simp only [Set.mem_Ici, sub_nonneg]; linarith
    simp only [Set.mem_Ici, sub_nonneg]; linarith
    linarith
  apply this
  simp only [Set.mem_Ici]; linarith
  simp only [Set.mem_Ici]; linarith
  assumption

private lemma mainlem64 (hd : 0 < Δ) (ht0 : 0 ≤ t) (htp : t ≤ ΔP) (htr : t ≤ r)
    (htd : r ≤ Δ) (hΔ : ΔP ≤ Δ) : (Wp c Δ) r t ≤ (Wp c Δ) Δ ΔP := by
  have first : (Wp c Δ) r t ≤ (Wp c Δ) Δ t := monoWp2 hd ht0 htr htd
  have second : (Wp c Δ) Δ t ≤ (Wp c Δ) Δ ΔP := monoWp1 hd hΔ htp
  linarith

private lemma W_pos (hd : 0 < Δ) (ht0 : 0 ≤ t) (htr : t ≤ r) : 0 ≤ Wp c Δ r t := by
  have e0 : 0 = Wp c Δ r 0 := by unfold Wp; field_simp
  rw [e0]; apply monoWp1 hd htr ht0

private lemma W_eq_Q_Δ (hΔ : 0 < Δ) : 1 - Qp Δ c (Δ - ΔP) = (Wp c Δ) Δ ΔP := by
  unfold Wp Qp
  have ep : Ep c Δ > 0 := by apply Ep_r_pos; linarith
  field_simp

private lemma W_eq_Q (hΔ : 0 < Δ) : Qp Δ c r - Qp Δ c rr = Wp c Δ r (r - rr) := by
  unfold Wp Qp; simp only [sub_sub_cancel]
  have ep : Ep c Δ > 0 := by apply Ep_r_pos; linarith
  field_simp

lemma lemma64sub (hd : 0 < Δ) (ht0: 0 ≤ r - rr) (htp: r - rr ≤ ΔP) (hrr: 0 ≤ rr)
    (htd: r ≤ Δ) (hΔ : ΔP ≤ Δ ) : |Qp Δ c r - Qp Δ c rr| ≤ 1 - Qp Δ c (Δ - ΔP) := by
  have e1 : |Qp Δ c r - Qp Δ c rr| = Qp Δ c r - Qp Δ c rr := by
    apply abs_of_nonneg; rw [W_eq_Q]; apply W_pos
    any_goals linarith
  rw [e1, W_eq_Q_Δ, W_eq_Q ]
  apply mainlem64
  any_goals linarith

lemma Lemma64 (hc : c ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) (hΔ : ΔP < Δ) (hΔP : 0 < ΔP) :
    |Qp Δ c r - Qp Δ c (Int.floor (r / ΔP) * ΔP)| ≤ 1 - Qp_lo Δ (Δ - ΔP) := by
  have i00 : (Int.floor (r / ΔP) * ΔP) ≥ 0 := by
    apply mul_nonneg; simp; apply Int.floor_nonneg.mpr
    apply div_nonneg
    any_goals linarith
  have i01 : r - (Int.floor (r / ΔP) * ΔP) ≥ 0 := by
    simp
    have i2 : Int.floor (r / ΔP) * ΔP ≤ r / ΔP * ΔP := by
      apply mul_le_mul; apply Int.floor_le; simp; linarith
      apply div_nonneg
      any_goals linarith
    have e0 : r / ΔP * ΔP = r := by field_simp
    linarith
  have i02 : r - (Int.floor (r / ΔP) * ΔP) <  ΔP := by
    have i1 : Int.floor (r / ΔP) +1 > r / ΔP := by apply Int.lt_floor_add_one
    have i2 : Int.floor (r / ΔP) * ΔP > (r/ΔP -1)* ΔP := by
      apply mul_lt_mul; linarith; simp; linarith; simp
      apply Int.floor_nonneg.mpr; apply div_nonneg; linarith;linarith
    have e1 : r - (r/ΔP -1)* ΔP = ΔP := by field_simp
    linarith
  have i1 : |Qp Δ c r - Qp Δ c (Int.floor (r / ΔP) * ΔP)| ≤ 1 - Qp Δ c (Δ - ΔP) := by
    apply lemma64sub
    any_goals linarith
  have i2 : Qp Δ c (Δ - ΔP) ≥  Qp_lo Δ (Δ - ΔP) := by apply q_lower_bound; assumption; linarith; linarith
  linarith
