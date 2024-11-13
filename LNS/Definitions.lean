import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace LNS

noncomputable section

/- A model of fixed-point arithmetic -/
structure FixedPoint where
  ε : ℝ
  rnd : ℝ → ℝ
  hrnd : ∀ x, |x - rnd x| ≤ ε
  rnd_mono : Monotone rnd
  rnd_1 : rnd 1 = 1
  rnd_0 : rnd 0 = 0

lemma fix_hrnd_sym (fix : FixedPoint) : ∀ x : ℝ, |fix.rnd x - x| ≤ fix.ε := by
  intro x; rw [abs_sub_comm]; exact fix.hrnd x

/- FunApprox f s models an approximation of a function f on s -/
structure FunApprox (f : ℝ → ℝ) (s : Set ℝ) where
  fe : ℝ → ℝ
  err : ℝ
  herr : ∀ x ∈ s, |fe x - f x| ≤ err

instance : CoeFun (FunApprox f s) (fun _ => ℝ → ℝ) where
  coe fapprox := fapprox.fe

lemma funApprox_err_sym (g : FunApprox f s) :
    ∀ x ∈ s, |f x - g x| ≤ g.err := by
  intro x xs; rw [abs_sub_comm]; exact g.herr x xs

open Real

/- Φ⁺ and Φ⁻ from Introduction -/

def Φp (x : ℝ) := logb 2 (1 + (2 : ℝ) ^ x)

def Φm (x : ℝ) := logb 2 (1 - (2 : ℝ) ^ x)

/- Iₓ and Rₓ correspond to iₓ and rₓ from Eq (1) -/

def Iₓ (Δ x : ℝ) := ⌈x / Δ⌉ * Δ

def Rₓ (Δ x : ℝ) := Iₓ Δ x - x

/- E i r is the error of the first order Taylor approximation
   defined for all real i and r -/

def Ep (i r : ℝ) := Φp (i - r) - Φp i + r * deriv Φp i

def Em (i r : ℝ) := -Φm (i - r) + Φm i - r * deriv Φm i

def Ep_i (r: ℝ):= fun i => Ep i r

def Em_i (r: ℝ):= fun i => Em i r

def Qp (Δ i r : ℝ) := Ep i r / Ep i Δ

def Qp_lo (Δ r : ℝ) := Qp Δ 0 r

def Qp_hi (Δ r : ℝ) := (2 ^ (-r) + r * log 2 - 1) / (2 ^ (-Δ) + Δ * log 2 - 1)

def Rp_opt (Δ : ℝ) :=
  let X := 2 ^ Δ
  let A (Y : ℝ) := -2*Y*(log (Y+1) - log Y - log 2) - Y + 1
  let B (Y : ℝ) := Y*(2* log (Y+1) - log Y - 2 * log 2)
  logb 2 (B X / A X)

def Qm (Δ i r : ℝ) := Em i r / Em i Δ

def Qm_hi (Δ i r : ℝ) := Qm Δ i r

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

variable (fix : FixedPoint)

def Ep_fix (i r : ℝ) := Φp (i - r) - fix.rnd (Φp i) + fix.rnd (r * fix.rnd (deriv Φp i))

def Em_fix (i r : ℝ) := Φm (i - r) - fix.rnd (Φm i) + fix.rnd (r * fix.rnd (deriv Φm i))

def ΦTp_fix (Δ x : ℝ) := fix.rnd (Φp (Iₓ Δ x)) - fix.rnd (Rₓ Δ x * fix.rnd (deriv Φp (Iₓ Δ x)))

def ΦTm_fix (Δ x : ℝ) := fix.rnd (Φm (Iₓ Δ x)) - fix.rnd (Rₓ Δ x * fix.rnd (deriv Φm (Iₓ Δ x)))


def EECp (Δ ΔP c i r  : ℝ) :=
  fix.rnd (Φp i) - fix.rnd (r * fix.rnd (deriv Φp i) )
                 + fix.rnd (fix.rnd (Ep i Δ) * fix.rnd (Qp Δ c (⌊r / ΔP⌋ * ΔP)))

def EECp_fix (Δ ΔP c i r  : ℝ):= Φp (i - r) - EECp fix Δ ΔP c i r

def EECm (Δ ΔP c i r : ℝ) :=
  fix.rnd (Φm i) - fix.rnd (r * fix.rnd (deriv Φm i) )
                 - fix.rnd (fix.rnd (Em i Δ) * fix.rnd (Qm Δ c (⌊r / ΔP⌋ * ΔP)))

def EECm_fix (Δ ΔP c i r  : ℝ):= Φm (i - r) - EECm fix Δ ΔP c i r

def ΦECp_fix (Δ ΔP c x : ℝ) := EECp fix Δ ΔP c (Iₓ Δ x) (Rₓ Δ x)

def ΦECm_fix (Δ ΔP c x : ℝ) := EECm fix Δ ΔP c (Iₓ Δ x) (Rₓ Δ x)

end FixedPoint
