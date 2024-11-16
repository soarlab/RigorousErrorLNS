import LNS.Definitions
import LNS.BasicIxRx
import LNS.Lemma51
import LNS.Lemma52

namespace LNS

theorem Theorem53_Ep (fix : FixedPoint) {i r Δ : ℝ} (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    |Ep_fix fix i r| < (Ep 0 Δ) + (2 + Δ) * fix.ε := by
  set s1 := (Φp i - fix.rnd (Φp i))
  set s2 := r * (fix.rnd (deriv Φp i) - deriv Φp i)
  set s3 := (fix.rnd (r * fix.rnd (deriv Φp i)) - r * fix.rnd (deriv Φp i))
  have e1 : Ep_fix fix i r = Ep i r + s1 + s2 + s3 := by unfold Ep_fix Ep; ring_nf
  have i1 : |s1| ≤ fix.ε := by apply fix.hrnd
  have i3 : |s3| ≤ fix.ε := by
    have : |s3| = |r * fix.rnd (deriv Φp i) - fix.rnd (r * fix.rnd (deriv Φp i))| := by apply abs_sub_comm
    rw [this]
    apply fix.hrnd
  have i2 : |s2| ≤ Δ * fix.ε := by
    have e1 : |s2| = |r| * |(fix.rnd (deriv Φp i) - deriv Φp i)| := by apply abs_mul
    have e2 : |(fix.rnd (deriv Φp i) - deriv Φp i)| = |(deriv Φp i) - fix.rnd (deriv Φp i)| := by apply abs_sub_comm
    have e3 : |r| = r := by apply abs_of_nonneg; linarith
    rw [e1, e2, e3]
    have i21 : |deriv Φp i - fix.rnd (deriv Φp i)| ≤ fix.ε := by apply fix.hrnd
    apply mul_le_mul (le_of_lt hr2) i21; simp; linarith
  have i0 : |Ep_fix fix i r| ≤ |Ep i r| + |s1| + |s2| + |s3| := by
    have i01 : |Ep_fix fix i r| ≤ |Ep i r + s1 + s2| + |s3| := by rw [e1]; apply abs_add
    have i02 : |Ep i r + s1 + s2|  ≤    |Ep i r + s1| + |s2| := by apply abs_add
    have i03 : |Ep i r + s1|  ≤ |Ep i r| + |s1| := by apply abs_add
    linarith
  have i01 : |Ep i r| < Ep 0 Δ := by exact Lemma51 hi hr1 hr2
  linarith

theorem Theorem53_Em (fix : FixedPoint) {i₀ i r Δ : ℝ} (hi₀ : i₀ < 0) (hi : i ≤ i₀) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    |Em_fix fix i r| < (Em i₀ Δ) + (2 + Δ) * fix.ε := by
  set s1 := (Φm i - fix.rnd (Φm i))
  set s2 := r*(fix.rnd (deriv Φm i) - deriv Φm i)
  set s3 := (fix.rnd (r * fix.rnd (deriv Φm i)) - r * fix.rnd (deriv Φm i))
  have e1 : Em_fix fix i r = (-Em i r) + s1 + s2 + s3 := by unfold Em_fix Em; ring_nf
  have i1 : |s1| ≤ fix.ε := by apply fix.hrnd
  have i3 : |s3| ≤ fix.ε := by
    have : |s3| = |r * fix.rnd (deriv Φm i) - fix.rnd (r * fix.rnd (deriv Φm i))| := by apply abs_sub_comm
    rw [this]
    apply fix.hrnd
  have i2 : |s2| ≤ Δ*fix.ε := by
    have e1 : |s2| = |r| * |(fix.rnd (deriv Φm i) - deriv Φm i)| := by apply abs_mul
    have e2 : |(fix.rnd (deriv Φm i) - deriv Φm i)| = |(deriv Φm i) - fix.rnd (deriv Φm i)| := by apply abs_sub_comm
    have e3 : |r| = r := by apply abs_of_nonneg; linarith
    rw [e1, e2, e3]
    have i21 : |deriv Φm i - fix.rnd (deriv Φm i)| ≤ fix.ε := by apply fix.hrnd
    apply mul_le_mul (le_of_lt hr2) i21; simp; linarith
  have i0 : |Em_fix fix i r| ≤ |Em i r| + |s1| + |s2| + |s3| := by
    have i01 : |Em_fix fix i r| ≤ |-Em i r + s1 + s2| + |s3| := by rw [e1]; apply abs_add
    have i02 : |-Em i r + s1 + s2| ≤ |-Em i r + s1| + |s2| := by apply abs_add
    have i03 : |-Em i r + s1| ≤ |-Em i r| + |s1| := by apply abs_add
    have i04 : |-Em i r| =|Em i r| := by apply abs_neg
    linarith
  have i01 : |Em i r| < Em i₀ Δ := by exact Lemma52 hi₀ hi hr1 hr2
  linarith

/- A linear Taylor approximation error bound for Φ⁺ -/

theorem Theorem53_ΦTp (fix : FixedPoint) {x Δ : ℝ} (hd : 0 < Δ) (hx : x ≤ 0) :
    |Φp x - ΦTp_fix fix Δ x| < Ep 0 Δ + (2 + Δ) * fix.ε := by
  have eq : Φp x - ΦTp_fix fix Δ x = Ep_fix fix (Iₓ Δ x) (Rₓ Δ x) := by
    unfold ΦTp_fix Ep_fix; rw [i_sub_r_eq_x]; ring_nf
  rw [eq]
  apply Theorem53_Ep fix _ (rx_nonneg hd x) (rx_lt_delta hd x)
  rw [← x_neg_iff_ix_neg hd]; exact hx

/- A linear Taylor approximation error bound for Φ⁻ -/

theorem Theorem53_ΦTm (fix : FixedPoint) {x₀ x Δ : ℝ} (hd : 0 < Δ) (hx₀ : x₀ ≤ -Δ) (hx : x ≤ x₀) :
    |Φm x - ΦTm_fix fix Δ x| < Em (Iₓ Δ x₀) Δ + (2 + Δ) * fix.ε := by
  have eq : Φm x - ΦTm_fix fix Δ x = Em_fix fix (Iₓ Δ x) (Rₓ Δ x) := by
    unfold ΦTm_fix Em_fix; rw [i_sub_r_eq_x]; ring_nf
  rw [eq]
  exact Theorem53_Em fix (ix_lt_zero hd hx₀) (ix_monotone hd hx) (rx_nonneg hd x) (rx_lt_delta hd x)

/- This theorem corresponds to the approximation theorem in the paper -/

theorem Theorem53_ΦTm' (fix : FixedPoint) {x Δ : ℝ}
    (hdn : ∃ n : ℕ, 1 = n * Δ) (hx : x ≤ -1) :
    |Φm x - ΦTm_fix fix Δ x| < Em (-1) Δ + (2 + Δ) * fix.ε := by
  have hx₀ : -1 ≤ -Δ := by rw [neg_le_neg_iff]; exact div_one_imp_le_one hdn
  rw [← ix_eq_neg_one hdn]
  apply Theorem53_ΦTm fix (div_one_imp_pos hdn) hx₀ hx

/- Taylor approximations of Φ⁺ and Φ⁻ -/

noncomputable def ΦTp_approx (fix : FixedPoint) {Δ : ℝ} (hd : 0 < Δ) : FunApprox Φp (Set.Iic 0) := {
  fe := ΦTp_fix fix Δ
  err := Ep 0 Δ + (2 + Δ) * fix.ε
  herr := fun _ => le_of_lt ∘ Theorem53_ΦTp fix hd
}

noncomputable def ΦTm_approx (fix : FixedPoint) {Δ : ℝ} (hdn : ∃ n : ℕ, 1 = n * Δ) : FunApprox Φm (Set.Iic (-1)) := {
  fe := ΦTm_fix fix Δ
  err := Em (-1) Δ + (2 + Δ) * fix.ε
  herr := fun _ => le_of_lt ∘ Theorem53_ΦTm' fix hdn
}
