/- This file contains all main results -/

import LNS.Definitions
import LNS.Theorem53
import LNS.Theorem68

open LNS

/- First order Taylor approximations -/

theorem TaylorApprox_Φp (fix : FixedPoint) {x Δ : ℝ} (hd : 0 < Δ) (hx : x ≤ 0) :
    |Φp x - ΦTp_fix fix Δ x| ≤ Ep 0 Δ + (2 + Δ) * fix.ε := Theorem53_ΦTp fix hd hx

theorem TaylorApprox_Φm (fix : FixedPoint) {x Δ : ℝ}
    (hdn : ∃ n : ℕ, 1 = n * Δ) (hx : x ≤ -1) :
    |Φm x - ΦTm_fix fix Δ x| ≤ Em (-1) Δ + (2 + Δ) * fix.ε := Theorem53_ΦTm' fix hdn hx

/- Error correction approximations -/

theorem ErrorCorrection_Φp (fix : FixedPoint) (hc : c ≤ 0) (hΔ : ΔP < Δ)
    (hΔP : 0 < ΔP) (hx : x ≤ 0) :
    |Φp x - ΦECp_fix fix Δ ΔP c x| ≤ (4 + Δ) * fix.ε + Ep 0 Δ * (QRp Δ + QIp Δ ΔP + fix.ε) :=
  Theorem68_ΦECp fix hc hΔ hΔP hx

theorem ErrorCorrection_Φm (fix : FixedPoint) {Δ ΔP : ℝ} (hc : c ≤ -1) (hΔ : ΔP < Δ)
    (hΔP : 0 < ΔP) (hdn : ∃ n : ℕ, 1 = n * Δ) (hx : x ≤ -1) :
    |Φm x - ΦECm_fix fix Δ ΔP c x| ≤ (4 + Δ) * fix.ε + Em (-1) Δ * (QRm Δ + QIm Δ ΔP + fix.ε) :=
  Theorem68_ΦECm fix hc hΔ hΔP hdn hx

/- All theorems depend on standard axioms only: [propext, Classical.choice, Quot.sound]-/

#print axioms TaylorApprox_Φp
#print axioms TaylorApprox_Φm
#print axioms ErrorCorrection_Φp
#print axioms ErrorCorrection_Φm
