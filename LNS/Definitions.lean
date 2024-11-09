import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace LNS

noncomputable section

open Real

/- Φ⁺ and Φ⁻ from Introduction -/

def Φp (x : ℝ) := logb 2 (1 + (2 : ℝ) ^ x)

def Φm (x : ℝ) := logb 2 (1 - (2 : ℝ) ^ x)

/- Iₓ and Rₓ correspond to iₓ and rₓ from Eq (1) -/

def Iₓ (Δ x : ℝ) := ⌈x / Δ⌉ * Δ

def Rₓ (Δ x : ℝ) := Iₓ Δ x - x

/- Φₜ is the first order Taylor approximation of Φ⁺ from Eq (1) -/

def ΦTp (Δ x : ℝ) := Φp (Iₓ Δ x) - Rₓ Δ x * deriv Φp (Iₓ Δ x)

/- E i r is the error of the first order Taylor approximation
   defined for all real i and r -/

def Ep (i r : ℝ) := Φp (i - r) - Φp i + r * deriv Φp i

def Em (i r : ℝ) := -Φm (i - r) + Φm i - r * deriv Φm i

def Qp (Δ i r : ℝ) := Ep i r / Ep i Δ

def Qp_lo (Δ r : ℝ) := Qp Δ 0 r

def Qp_hi (Δ r : ℝ) := (2 ^ (-r) + r * log 2 - 1) / (2 ^ (-Δ) + Δ * log 2 - 1)

def Rp_opt (Δ : ℝ) :=
  let X := 2 ^ Δ
  let A (Y : ℝ) := -2*Y*(log (Y+1) - log Y - log 2) - Y + 1
  let B (Y : ℝ) := Y*(2* log (Y+1) - log Y - 2 * log 2)
  logb 2 (B X / A X)

def Qm (Δ i r : ℝ) := Em i r / Em i Δ

def Qm_hi (Δ r : ℝ) := Qm Δ (-1) r

def Qm_lo (Δ r : ℝ) := (2 ^ (-r) + r * log 2 - 1) / (2 ^ (-Δ) + Δ * log 2 - 1)

def Rm_opt (Δ : ℝ) :=
  let X := 2 ^ Δ
  let Vm (X:ℝ) := 2*log X - log (2*X-1)
  let Am (Y:ℝ) := 2*Y*log Y - 2*Y*log (2*Y-1) + 2*Y  -2
  let Bm (Y:ℝ) := Y*(Vm Y)
  logb 2 (Bm X / Am X)

/-
  Fixed-point rounding
-/

section FixedPoint

structure FixedPoint where
  ε : ℝ
  rnd : ℝ → ℝ
  hrnd : ∀ x, |x - rnd x| ≤ ε
  rnd_mono : Monotone rnd
  rnd_1 : rnd 1 = 1
  rnd_0 : rnd 0 = 0

variable (fix : FixedPoint)

def Ep_fix (i r : ℝ) := Φp (i - r) - fix.rnd (Φp i) + fix.rnd (r * fix.rnd (deriv Φp i))

def Em_fix (i r : ℝ) := Φm (i - r) - fix.rnd (Φm i) + fix.rnd (r * fix.rnd (deriv Φm i))

def EECp (Δ ΔP c i r  : ℝ) :=
  fix.rnd (Φp i) - fix.rnd (r * fix.rnd (deriv Φp i) )
                 + fix.rnd (fix.rnd (Ep i Δ) * fix.rnd (Qp Δ c (Int.floor (r / ΔP) * ΔP)))

def EECfixp (Δ ΔP c i r  : ℝ):= |Φp (i - r) - EECp fix Δ ΔP c i r|

def EECm (Δ ΔP c i r  : ℝ) :=
  fix.rnd (Φm i) - fix.rnd (r * fix.rnd (deriv Φm i) )
                 - fix.rnd (fix.rnd (Em i Δ) * fix.rnd (Qm Δ c (Int.floor (r / ΔP) * ΔP)))

def EECfixm (Δ ΔP c i r  : ℝ):= |Φm (i - r) - EECm fix Δ ΔP c i r|

end FixedPoint
