import LNS.Tactic
import LNS.Definitions
import LNS.Lemma63
import LNS.Lemma66

namespace LNS

noncomputable section

open Real

private def Wm c Δ r t := (Em c r - Em c (r-t)) / Em c Δ

private def Wtm c Δ t r := Wm c Δ r t

private lemma monoWm1 (hd : 0 < Δ) (hc : c < 0) (h1 : ΔP ≤ r) (htp : t ≤ ΔP) :
    (Wm c Δ) r t ≤  (Wm c Δ) r ΔP := by
  have ep : Em c Δ > 0 := Em_r_pos hc hd
  unfold Wm; rw [div_le_div_iff_of_pos_right ep]; apply sub_le_sub_left
  apply Em_r_monotoneOn hc (by simp; linarith) (by simp; linarith) (by linarith)

private lemma monoWm2 (hd : 0 < Δ) (hc : c < 0) (ht : 0 ≤ t) (htr : t ≤ r) (htd : r ≤ Δ) :
    (Wm c Δ) r t ≤ (Wm c Δ) Δ t := by
  have hc0 : c ∈ Set.Iio 0 := by simp only [Set.mem_Iio]; linarith
  have ep : Em c Δ > 0 := Em_r_pos hc hd
  unfold Wm; rw [div_le_div_iff_of_pos_right ep]
  have ec2 : (fun y ↦ Em c (y - t)) = (fun y => Em c y) ∘ (fun y => y - t) := by ext y; simp only [Function.comp_apply]
  have mt : Set.MapsTo (fun y ↦ y - t) (Set.Ioi t) (Set.Ioi 0) := by
    unfold Set.MapsTo; intro x hx; simp only [Set.mem_Ioi] at hx; simp only [Set.mem_Ioi, sub_nonneg, hx]; linarith
  have diff : DifferentiableOn ℝ (fun x => Em c x - Em c (x - t))  (Set.Ioi t) := by
    apply DifferentiableOn.sub
    apply DifferentiableOn.mono (differentiableOn_Em_r hc0)
    simp only [Set.Ioi_subset_Ioi_iff]; exact ht
    rw [ec2]; apply DifferentiableOn.comp (differentiableOn_Em_r hc0) _ mt
    simp only [differentiableOn_const, DifferentiableOn.sub_iff_left]
    exact differentiableOn_id
  have cont : ContinuousOn (fun x => Em c x - Em c (x - t))  (Set.Ici t) := by
    apply ContinuousOn.sub
    apply ContinuousOn.mono (continuousOn_Em_r hc0)
    rw [Set.Ici_subset_Ici]; exact ht
    rw [ec2]
    apply ContinuousOn.comp (continuousOn_Em_r hc0)
    apply ContinuousOn.sub continuousOn_id continuousOn_const
    unfold Set.MapsTo; intro x hx; simp only [Set.mem_Ici] at hx; simp only [Set.mem_Ici, sub_nonneg, hx]
  have : MonotoneOn (fun x => Em c x - Em c (x - t))  (Set.Ici t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici t) cont
    apply DifferentiableOn.mono diff
    simp only [Set.nonempty_Iio, interior_Ici', subset_refl]
    intro x hx
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
    rw [deriv_sub, ec2, deriv_comp]
    simp only [differentiableAt_id', differentiableAt_const, deriv_sub, deriv_id'', deriv_const',
      sub_zero, mul_one, sub_nonneg]
    rw [(by simp only: (fun y ↦ Em c y) = Em c)]
    apply (StrictMonoOn.monotoneOn (deriv_Em_r_strictMono hc0))
    simp only [Set.mem_Ioi, sub_nonneg]; linarith
    simp only [Set.mem_Ioi, sub_nonneg]; linarith
    linarith
    apply DifferentiableOn.differentiableAt (differentiableOn_Em_r hc0)
    apply Ioi_mem_nhds; linarith
    simp only [differentiableAt_id', differentiableAt_const, DifferentiableAt.sub]
    apply DifferentiableOn.differentiableAt (differentiableOn_Em_r hc0)
    apply Ioi_mem_nhds; linarith
    rw [ec2]; apply DifferentiableAt.comp
    apply DifferentiableOn.differentiableAt (differentiableOn_Em_r hc0)
    apply Ioi_mem_nhds; linarith
    apply DifferentiableAt.sub differentiableAt_id (by simp only [differentiableAt_const])
  apply this
  simp only [Set.mem_Ici]; linarith
  simp only [Set.mem_Ici]; linarith
  assumption

private lemma mainlem67 (hd : 0 < Δ) (hc : c < 0) (ht0 : 0 ≤ t) (htp : t ≤ ΔP) (htr : t ≤ r)
    (htd : r ≤ Δ) (hΔ : ΔP ≤ Δ) : (Wm c Δ) r t ≤ (Wm c Δ) Δ ΔP := by
  have first : (Wm c Δ) r t ≤ (Wm c Δ) Δ t := monoWm2 hd hc ht0 htr htd
  have second : (Wm c Δ) Δ t ≤ (Wm c Δ) Δ ΔP := monoWm1 hd hc hΔ htp
  linarith

private lemma Wm_pos (hd : 0 < Δ) (hc : c < 0) (ht0 : 0 ≤ t) (htr : t ≤ r) : 0 ≤ Wm c Δ r t := by
  have e0 : 0 = Wm c Δ r 0 := by unfold Wm; field_simp
  rw [e0]; apply monoWm1 hd hc htr ht0

private lemma Wm_eq_Qm_Δ (hΔ : 0 < Δ) (hc : c < 0) : 1 - Qm Δ c (Δ - ΔP) = (Wm c Δ) Δ ΔP := by
  unfold Wm Qm
  have ep : Em c Δ > 0 := by apply Em_r_pos _ hΔ; linarith
  field_simp

private lemma Wm_eq_Qm (hΔ : 0 < Δ) (hc : c < 0) : Qm Δ c r - Qm Δ c rr = Wm c Δ r (r - rr) := by
  unfold Wm Qm; simp only [sub_sub_cancel]
  have ep : Em c Δ > 0 := by apply Em_r_pos _ hΔ; linarith
  field_simp

lemma lemma67sub (hd : 0 < Δ) (hc : c < 0) (ht0 : 0 ≤ r - rr) (htp : r - rr ≤ ΔP) (hrr : 0 ≤ rr)
    (htd : r ≤ Δ) (hΔ : ΔP ≤ Δ) : |Qm Δ c r - Qm Δ c rr| ≤ 1 - Qm Δ c (Δ - ΔP) := by
  have e1 : |Qm Δ c r - Qm Δ c rr| = Qm Δ c r - Qm Δ c rr := by
    apply abs_of_nonneg; rw [Wm_eq_Qm]; apply Wm_pos
    any_goals linarith
  rw [e1, Wm_eq_Qm_Δ, Wm_eq_Qm ]
  apply mainlem67
  any_goals linarith

lemma Lemma67 (hc : c < 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) (hΔ : ΔP < Δ) (hΔP : 0 < ΔP) :
    |Qm Δ c r - Qm Δ c (Int.floor (r / ΔP) * ΔP)| ≤ 1 - Qm_lo Δ (Δ - ΔP) := by
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
  have i1 : |Qm Δ c r - Qm Δ c (Int.floor (r / ΔP) * ΔP)| ≤ 1 - Qm Δ c (Δ - ΔP) := by
    apply lemma67sub (by linarith) hc i01 (by linarith) i00 (by linarith) (by linarith)
  have i2 : Qm Δ c (Δ - ΔP) ≥  Qm_lo Δ (Δ - ΔP) := by
    apply qm_lower_bound hc (le_refl c) (by linarith) (by linarith)
  linarith
