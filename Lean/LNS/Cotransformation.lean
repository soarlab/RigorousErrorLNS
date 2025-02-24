import LNS.Definitions
import LNS.BasicIxRx
import LNS.BasicRounding
import LNS.BasicPhi
import LNS.BasicCotrans

namespace LNS

noncomputable section

open Real

/- Case 2 -/

section Cotrans2

lemma bound_case2 (fix : FixedPoint)
    (hc : c < 0) (Φe : FunApprox Φm (Set.Iic c))
    (ha : 0 < Δa) (hx : x < 0) (hk : kval Δa x ≤ c)
    (hkr : krnd fix Δa x ≤ c) (hkr2 : |kval Δa x - krnd fix Δa x| ≤ kε):
    |Φm x - Cotrans₂ fix Φe Δa x| ≤ fix.ε + Φm (c - kε) - Φm c + Φe.err := by
  rw [cotransformation ha hx]
  set s1 := Φm (ind Δa x) - fix.rnd (Φm (ind Δa x) )
  set s2 := Φm (kval Δa x) - Φm (krnd fix Δa x)
  set s3 := Φm (krnd fix Δa x) - Φe (krnd fix Δa x)
  have eq : Φm (ind Δa x) + Φm (kval Δa x) - Cotrans₂ fix Φe Δa x = s1 + s2 + s3 := by
    unfold Cotrans₂; ring_nf
  rw [eq]
  have i01 : |s1 + s2 + s3| ≤ |s1 + s2| + |s3| := by apply abs_add
  have i02 : |s1 + s2| ≤ |s1| + |s2| := by apply abs_add
  have i1 : |s1| ≤ fix.ε := by apply fix.hrnd
  have i3 : |s3| ≤ Φe.err := by apply Φe.herr; apply hkr
  have i2 : |s2| ≤ Φm (c - kε) - Φm c := cotrans_lemma hc hk hkr hkr2
  linarith

theorem cotransformation_case2 (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1))) /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa)
    (hΔa : 4 * fix.ε ≤ Δa)             /- Δa should be large enough -/
    (hx : x ≤ -Δa) :                   /- The result is valid for all x ∈ (-∞, -Δa] -/
    |Φm x - Cotrans₂ fix Φe Δa x| ≤ fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err := by
  apply bound_case2 fix neg_one_lt_zero Φe ha (by linarith : x < 0)
  · exact k_bound'' ha hx
  · linarith [krnd_bound fix ha hx]
  · exact krnd_fix_bound fix _ _

/- A simplified error bound -/
theorem cotransformation_case2' (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1))) /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa)
    (hΔa : 4 * fix.ε ≤ Δa)             /- Δa should be large enough -/
    (hx : x ≤ -Δa) :                   /- The result is valid for all x ∈ (-∞, -Δa] -/
    |Φm x - Cotrans₂ fix Φe Δa x| ≤ 3 * fix.ε + Φe.err := by
  apply le_trans (cotransformation_case2 fix Φe ha hΔa hx)
  have ineq := phi_sub_phi_bound' (by linarith [fix.eps_nonneg] : 0 ≤ 2 * fix.ε)
  linarith

theorem cotransformation_case2_dir (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1))) /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa)
    (hΔa : 2 * fix.ε ≤ Δa)             /- Δa should be large enough -/
    (hx : x ≤ -Δa) :                   /- The result is valid for all x ∈ (-∞, -Δa] -/
    |Φm x - Cotrans₂ fix Φe Δa x| ≤ fix.ε + Φm (-1 - fix.ε) - Φm (-1) + Φe.err := by
  apply bound_case2 fix neg_one_lt_zero Φe ha (by linarith : x < 0)
  · exact k_bound'' ha hx
  · linarith [krnd_bound_dir fix ha hx]
  · exact krnd_fix_bound_dir fix _ _

/- A simplified error bound (directed rounding) -/
theorem cotransformation_case2_dir' (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1))) /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa)
    (hΔa : 2 * fix.ε ≤ Δa)             /- Δa should be large enough -/
    (hx : x ≤ -Δa) :                   /- The result is valid for all x ∈ (-∞, -Δa] -/
    |Φm x - Cotrans₂ fix Φe Δa x| ≤ 2 * fix.ε + Φe.err := by
  apply le_trans (cotransformation_case2_dir fix Φe ha hΔa hx)
  have ineq := phi_sub_phi_bound' fix.eps_nonneg
  linarith

end Cotrans2

/- Case 3 -/

section Contrans3

lemma k2_alt (ha : 0 < Δa) (hb : 0 < Δb) : k₂ Δb x = x + Φm (rb Δa Δb x) + Φm (k₁ Δa Δb x) - Φm (ind Δb x) := by
  have e2 : Φm (rem Δb x) = Φm (rb Δa Δb x) + Φm (k₁ Δa Δb x) := by
    rw [cotransformation ha (rem_lt_zero hb), rb, k₁, kval]
  unfold k₂ kval
  rw [e2]; ring

lemma cotrans3 (hb : 0 < Δb) (hx : x < 0) : Φm x = Φm (ind Δb x) + Φm (k₂ Δb x) :=
  by rw [cotransformation hb hx, k₂]

lemma k2rnd_fix_bound (fix : FixedPoint) (hc : c < 0) (Φe : FunApprox Φm (Set.Iic c))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hk1 : k₁ Δa Δb x ≤ c) (hk1r : k1rnd fix Δa Δb x ≤ c) :
    |k₂ Δb x - k2rnd fix Φe Δa Δb x| ≤ 2 * fix.ε +  Φm (c - 2 * fix.ε) - Φm c + Φe.err := by
  set a1 := Φm (rb Δa Δb x) - fix.rnd (Φm (rb Δa Δb x))
  set a2 := fix.rnd (Φm (ind Δb x)) - Φm (ind Δb x)
  set a3 := Φm (k₁ Δa Δb x) - Φm (k1rnd fix Δa Δb x)
  set a4 := Φm (k1rnd fix Δa Δb x) - Φe (k1rnd fix Δa Δb x)
  have e : k₂ Δb x - k2rnd fix Φe Δa Δb x = a1 + a2 + a3 + a4 := by
    unfold k2rnd; rw [k2_alt ha hb]; ring
  rw [e]
  have i00 : |a1 + a2 + a3 + a4| ≤ |a1 + a2 + a3| + |a4| := by apply abs_add
  have i01 : |a1 + a2 + a3| ≤ |a1 + a2| + |a3| := by apply abs_add
  have i02 : |a1 + a2| ≤ |a1| + |a2| := by apply abs_add
  have i1 : |a1| ≤ fix.ε := by apply fix.hrnd
  have i2 : |a2| ≤ fix.ε := by apply fix.hrnd_sym
  have i4 : |a4| ≤ Φe.err := by apply Φe.herr; apply hk1r
  have i3 : |a3| ≤  Φm (c - 2 * fix.ε) - Φm c := by
    apply cotrans_lemma hc hk1 hk1r
    apply krnd_fix_bound
  linarith

lemma k2rnd_fix_bound_dir (fix : FixedPointDir) (hc : c < 0) (Φe : FunApprox Φm (Set.Iic c))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hk1 : k₁ Δa Δb x ≤ c) (hk1r : k1rnd fix Δa Δb x ≤ c) :
    |k₂ Δb x - k2rnd fix Φe Δa Δb x| ≤ fix.ε +  Φm (c - fix.ε) - Φm c + Φe.err := by
  set a1 := Φm (rb Δa Δb x) - fix.rnd (Φm (rb Δa Δb x))
  set a2 := Φm (ind Δb x) - fix.rnd (Φm (ind Δb x))
  set a3 := Φm (k₁ Δa Δb x) - Φm (k1rnd fix Δa Δb x)
  set a4 := Φm (k1rnd fix Δa Δb x) - Φe (k1rnd fix Δa Δb x)
  have e : k₂ Δb x - k2rnd fix Φe Δa Δb x = (a1 - a2) + a3 + a4 := by
    unfold k2rnd; rw [k2_alt ha hb]; ring
  rw [e]
  have i00 : |(a1 - a2) + a3 + a4| ≤ |(a1 - a2) + a3| + |a4| := by apply abs_add
  have i01 : |(a1 - a2) + a3| ≤ |a1 - a2| + |a3| := by apply abs_add
  have i12 : |a1 - a2| ≤ fix.ε := fix.abs_rnd_sub_rnd _ _
  have i4 : |a4| ≤ Φe.err := by apply Φe.herr; apply hk1r
  have i3 : |a3| ≤  Φm (c - fix.ε) - Φm c := by
    apply cotrans_lemma hc hk1 hk1r
    apply krnd_fix_bound_dir
  linarith

lemma bound_case3 (fix : FixedPoint) (hc : c < 0) (Φe : FunApprox Φm (Set.Iic c))
    (hb : 0 < Δb) (hx : x < 0)
    (hk2 : k₂ Δb x ≤ c) (hk2r : k2rnd fix Φe Δa Δb x ≤ c)
    (hk2rnd : |k₂ Δb x - k2rnd fix Φe Δa Δb x| ≤ Ek2) :
    |Φm x - Cotrans₃ fix Φe Δa Δb x| ≤ fix.ε + Φm (c - Ek2) - Φm c + Φe.err := by
  rw [cotrans3 hb hx]
  set s1 := Φm (ind Δb x) - fix.rnd (Φm (ind Δb x))
  set s2 := Φm (k₂ Δb x) - Φm (k2rnd fix Φe Δa Δb x)
  set s3 := Φm (k2rnd fix Φe Δa Δb x) - Φe (k2rnd fix Φe Δa Δb x)
  have e : Φm (ind Δb x) +  Φm (k₂ Δb x) - Cotrans₃ fix Φe Δa Δb x = s1 + s2 + s3 := by
    unfold Cotrans₃; ring_nf
  rw [e]
  have i01 : |s1 + s2 + s3| ≤ |s1 + s2| + |s3| := by apply abs_add
  have i02 : |s1 + s2| ≤ |s1| + |s2| := by apply abs_add
  have i1 : |s1| ≤ fix.ε := by apply fix.hrnd
  have i3 : |s3| ≤ Φe.err := by apply Φe.herr; apply hk2r
  have i2 : |s2| ≤ Φm (c - Ek2) - Φm c := by apply cotrans_lemma hc hk2 hk2r hk2rnd
  linarith

/- Note: If rem Δb x ∈ (-Δa, 0) then use Contrans₂ fix Δb x
   since Φm (rem Δb x) can be computed directly from
   a table defined for all values in (-Δa, 0) -/

theorem cotransformation_case3 (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1)))  /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa) (hb : 0 < Δb) (hrem : rem Δb x ≤ -Δa)
    (hΔa : 4 * fix.ε ≤ Δa)              /- Δa should be large enough -/
    (hΔb : 8 * fix.ε + 2 * Φe.err ≤ Δb) /- Δb should be large enough -/
    (hx : x ≤ -Δb) :                    /- The result is valid for all x ∈ (-∞, -Δb] -/
    let Ek2 := 2 * fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err
    |Φm x - Cotrans₃ fix Φe Δa Δb x| ≤ fix.ε + Φm (-1 - Ek2) - Φm (-1) + Φe.err := by
  have hk1 : k₁ Δa Δb x ≤ -1 := by apply k_bound'' ha hrem
  have hk1r : k1rnd fix Δa Δb x ≤ -1 := by unfold k1rnd; linarith [krnd_bound fix ha hrem]
  have hk2 : k₂ Δb x ≤ -1 := by unfold k₂; exact k_bound'' hb hx
  have hk2rnd := k2rnd_fix_bound fix neg_one_lt_zero Φe ha hb hk1 hk1r
  apply bound_case3 fix neg_one_lt_zero Φe hb (by linarith) hk2 _ hk2rnd
  have ineq1 := (abs_le.mp $ k2rnd_fix_bound fix neg_one_lt_zero Φe ha hb hk1 hk1r).1
  have ineq2 := k_bound' hb hx
  have ineq3 := phi_sub_phi_bound' (by linarith [fix.eps_nonneg] : 0 ≤ 2 * fix.ε)
  unfold k₂ at ineq1
  linarith

theorem cotransformation_case3_dir (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1)))  /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa) (hb : 0 < Δb) (hrem : rem Δb x ≤ -Δa)
    (hΔa : 2 * fix.ε ≤ Δa)              /- Δa should be large enough -/
    (hΔb : 4 * fix.ε + 2 * Φe.err ≤ Δb) /- Δb should be large enough -/
    (hx : x ≤ -Δb) :                    /- The result is valid for all x ∈ (-∞, -Δb] -/
    let Ek2 := fix.ε + Φm (-1 - fix.ε) - Φm (-1) + Φe.err
    |Φm x - Cotrans₃ fix Φe Δa Δb x| ≤ fix.ε + Φm (-1 - Ek2) - Φm (-1) + Φe.err := by
  have hk1 : k₁ Δa Δb x ≤ -1 := by apply k_bound'' ha hrem
  have hk1r : k1rnd fix Δa Δb x ≤ -1 := by unfold k1rnd; linarith [krnd_bound_dir fix ha hrem]
  have hk2 : k₂ Δb x ≤ -1 := by unfold k₂; exact k_bound'' hb hx
  have hk2rnd := k2rnd_fix_bound_dir fix neg_one_lt_zero Φe ha hb hk1 hk1r
  apply bound_case3 fix neg_one_lt_zero Φe hb (by linarith) hk2 _ hk2rnd
  have ineq1 := (abs_le.mp $ k2rnd_fix_bound_dir fix neg_one_lt_zero Φe ha hb hk1 hk1r).1
  have ineq2 := k_bound' hb hx
  have ineq3 := phi_sub_phi_bound' fix.eps_nonneg
  unfold k₂ at ineq1
  linarith

/- A simplified error bound -/
theorem cotransformation_case3' (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1)))  /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa) (hb : 0 < Δb) (hrem : rem Δb x ≤ -Δa)
    (hΔa : 4 * fix.ε ≤ Δa)              /- Δa should be large enough -/
    (hΔb : 8 * fix.ε + 2 * Φe.err ≤ Δb) /- Δb should be large enough -/
    (hx : x ≤ -Δb) :                    /- The result is valid for all x ∈ (-∞, -Δb] -/
    |Φm x - Cotrans₃ fix Φe Δa Δb x| ≤ 5 * fix.ε + 2 * Φe.err := by
  have hk1 : k₁ Δa Δb x ≤ -1 := by apply k_bound'' ha hrem
  have hk1r : k1rnd fix Δa Δb x ≤ -1 := by unfold k1rnd; linarith [krnd_bound fix ha hrem]
  apply le_trans (cotransformation_case3 fix Φe ha hb hrem hΔa hΔb hx)
  have ineq1 : 0 ≤ 2 * fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err := by
    apply (le_trans (abs_nonneg $ k₂ Δb x - k2rnd fix Φe Δa Δb x))
    exact k2rnd_fix_bound fix neg_one_lt_zero Φe ha hb hk1 hk1r
  have ineq2 := phi_sub_phi_bound' ineq1
  have ineq3 := phi_sub_phi_bound' (by linarith [fix.eps_nonneg] : 0 ≤ 2 * fix.ε)
  linarith

theorem cotransformation_case3_dir' (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1)))  /- An approximation of Φm on (-∞, -1] -/
    (ha : 0 < Δa) (hb : 0 < Δb) (hrem : rem Δb x ≤ -Δa)
    (hΔa : 2 * fix.ε ≤ Δa)              /- Δa should be large enough -/
    (hΔb : 4 * fix.ε + 2 * Φe.err ≤ Δb) /- Δb should be large enough -/
    (hx : x ≤ -Δb) :                    /- The result is valid for all x ∈ (-∞, -Δb] -/
    |Φm x - Cotrans₃ fix Φe Δa Δb x| ≤ 3 * fix.ε + 2 * Φe.err := by
  have hk1 : k₁ Δa Δb x ≤ -1 := by apply k_bound'' ha hrem
  have hk1r : k1rnd fix Δa Δb x ≤ -1 := by unfold k1rnd; linarith [krnd_bound_dir fix ha hrem]
  apply le_trans (cotransformation_case3_dir fix Φe ha hb hrem hΔa hΔb hx)
  have ineq1 : 0 ≤ fix.ε + Φm (-1 - fix.ε) - Φm (-1) + Φe.err := by
    apply (le_trans (abs_nonneg $ k₂ Δb x - k2rnd fix Φe Δa Δb x))
    exact k2rnd_fix_bound_dir fix neg_one_lt_zero Φe ha hb hk1 hk1r
  have ineq2 := phi_sub_phi_bound' ineq1
  have ineq3 := phi_sub_phi_bound' fix.eps_nonneg
  linarith

end Contrans3

/- A general result -/

section Cotrans

private lemma contrans2_bound_le_cotrans3_bound (he : 0 ≤ e) (herr : 0 ≤ err) :
    let Ek2 := e + Φm (-1 - e) - Φm (-1) + err
    eps + Φm (-1 - e) - Φm (-1) + err ≤ eps + Φm (-1 - Ek2) - Φm (-1) + err := by
  apply add_le_add_right
  apply add_le_add_right
  apply add_le_add_left
  apply Φm_antitoneOn
  · simp; linarith [phi_sub_phi_nonneg he]
  · simp; linarith
  · linarith [phi_sub_phi_nonneg he]

theorem cotransformation_err_bound (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1)))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hΔa : 4 * fix.ε ≤ Δa)                /- Δa should be large enough -/
    (hΔb : 8 * fix.ε + 2 * Φe.err ≤ Δb) : /- Δb should be large enough -/
    let Ek2 := 2 * fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err
    |Φm x - Cotrans fix Φe Δa Δb x| ≤ fix.ε + Φm (-1 - Ek2) - Φm (-1) + Φe.err := by
  intro Ek2
  have hε := fix.eps_nonneg
  have herr : 0 ≤ Φe.err := by
    apply le_trans (abs_nonneg _) (Φe.herr (-1) _)
    simp only [Set.mem_Iic, le_refl]
  have ek2_nonneg : 0 ≤ Ek2 := by
    have := phi_sub_phi_nonneg (by linarith : 0 ≤ 2 * fix.ε)
    unfold Ek2; rw [add_sub_assoc]
    positivity
  unfold Cotrans
  split_ifs with hax hbx hrem
  · linarith [fix.hrnd (Φm x), phi_sub_phi_nonneg ek2_nonneg]
  · apply le_trans (cotransformation_case2 fix Φe ha hΔa (by linarith : x ≤ -Δa))
    exact contrans2_bound_le_cotrans3_bound (by positivity) herr
  · have ineq : 4 * fix.ε ≤ Δb := by linarith
    apply le_trans (cotransformation_case2 fix Φe hb ineq (by linarith : x ≤ -Δb))
    exact contrans2_bound_le_cotrans3_bound (by positivity) herr
  · exact cotransformation_case3 fix Φe ha hb (by linarith) hΔa hΔb (by linarith)

theorem cotransformation_err_bound_dir (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1)))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hΔa : 2 * fix.ε ≤ Δa)                /- Δa should be large enough -/
    (hΔb : 4 * fix.ε + 2 * Φe.err ≤ Δb) : /- Δb should be large enough -/
    let Ek2 := fix.ε + Φm (-1 - fix.ε) - Φm (-1) + Φe.err
    |Φm x - Cotrans fix Φe Δa Δb x| ≤ fix.ε + Φm (-1 - Ek2) - Φm (-1) + Φe.err := by
  intro Ek2
  have hε := fix.eps_nonneg
  have herr : 0 ≤ Φe.err := by
    apply le_trans (abs_nonneg _) (Φe.herr (-1) _)
    simp only [Set.mem_Iic, le_refl]
  have ek2_nonneg : 0 ≤ Ek2 := by
    have := phi_sub_phi_nonneg hε
    unfold Ek2; rw [add_sub_assoc]
    positivity
  unfold Cotrans
  split_ifs with hax hbx hrem
  · linarith [fix.hrnd (Φm x), phi_sub_phi_nonneg ek2_nonneg]
  · apply le_trans (cotransformation_case2_dir fix Φe ha hΔa (by linarith : x ≤ -Δa))
    exact contrans2_bound_le_cotrans3_bound (by positivity) herr
  · have ineq : 2 * fix.ε ≤ Δb := by linarith
    apply le_trans (cotransformation_case2_dir fix Φe hb ineq (by linarith : x ≤ -Δb))
    exact contrans2_bound_le_cotrans3_bound (by positivity) herr
  · exact cotransformation_case3_dir fix Φe ha hb (by linarith) hΔa hΔb (by linarith)

/- Simplified bounds -/

theorem cotransformation_err_bound' (fix : FixedPoint)
    (Φe : FunApprox Φm (Set.Iic (-1)))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hΔa : 4 * fix.ε ≤ Δa)                /- Δa should be large enough -/
    (hΔb : 8 * fix.ε + 2 * Φe.err ≤ Δb) : /- Δb should be large enough -/
    |Φm x - Cotrans fix Φe Δa Δb x| ≤ 5 * fix.ε + 2 * Φe.err := by
  have hε := fix.eps_nonneg
  have herr : 0 ≤ Φe.err := by
    apply le_trans (abs_nonneg _) (Φe.herr (-1) _)
    simp only [Set.mem_Iic, le_refl]
  unfold Cotrans
  split_ifs with hax hbx hrem
  · linarith [fix.hrnd (Φm x)]
  · linarith [cotransformation_case2' fix Φe ha hΔa (by linarith : x ≤ -Δa)]
  · have ineq : 4 * fix.ε ≤ Δb := by linarith
    have := cotransformation_case2' fix Φe hb ineq (by linarith : x ≤ -Δb)
    linarith
  · apply cotransformation_case3' fix Φe ha hb (by linarith) hΔa hΔb (by linarith)

theorem cotransformation_err_bound_dir' (fix : FixedPointDir)
    (Φe : FunApprox Φm (Set.Iic (-1)))
    (ha : 0 < Δa) (hb : 0 < Δb)
    (hΔa : 2 * fix.ε ≤ Δa)                /- Δa should be large enough -/
    (hΔb : 4 * fix.ε + 2 * Φe.err ≤ Δb) : /- Δb should be large enough -/
    |Φm x - Cotrans fix Φe Δa Δb x| ≤ 3 * fix.ε + 2 * Φe.err := by
  have hε := fix.eps_nonneg
  have herr : 0 ≤ Φe.err := by
    apply le_trans (abs_nonneg _) (Φe.herr (-1) _)
    simp only [Set.mem_Iic, le_refl]
  unfold Cotrans
  split_ifs with hax hbx hrem
  · linarith [fix.hrnd (Φm x)]
  · linarith [cotransformation_case2_dir' fix Φe ha hΔa (by linarith : x ≤ -Δa)]
  · have ineq : 2 * fix.ε ≤ Δb := by linarith
    have := cotransformation_case2_dir' fix Φe hb ineq (by linarith : x ≤ -Δb)
    linarith
  · apply cotransformation_case3_dir' fix Φe ha hb (by linarith) hΔa hΔb (by linarith)

end Cotrans
