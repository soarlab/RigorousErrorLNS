import LNS.Common
import LNS.Basic
import LNS.Lemma71
set_option maxHeartbeats 10000000

noncomputable section

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

open LNS
open Real
open Real Filter Topology

variable (fix : FixedPoint)

lemma hrndn : |fix.rnd x - x| ≤ fix.ε := by
  rw [abs_sub_comm]
  exact fix.hrnd x

/-Case 2-/

section Cotrans2

variable (Δa : ℝ)
variable (ha : Δa > 0)

def rb2 (x : ℝ) := (⌈x / Δa⌉ - 1) * Δa

def ra2 (x : ℝ) := rb2 Δa x - x

def k (x : ℝ) := x - Φm (rb2 Δa x)  + Φm (ra2 Δa x)

def Pestimate2 (x : ℝ) := Φm (rb2 Δa x) + Φm (k Δa x)

def krnd (x : ℝ) := x - fix.rnd (Φm (rb2 Δa x)) + fix.rnd (Φm (ra2 Δa x))

def Prnd2 (Φe : FunApprox Φm s) (x : ℝ) :=
  fix.rnd (Φm (rb2 Δa x)) + Φe (krnd fix Δa x)

include ha

lemma rb2_lt_x : rb2 Δa x < x:=by
  unfold rb2
  have i11: (⌈x / Δa⌉ - 1 < x / Δa) ∧ (x / Δa ≤ ⌈x / Δa⌉) := by
    apply Int.ceil_eq_iff.mp; simp
  have i1: ⌈x / Δa⌉ - 1 < x / Δa := i11.left
  have i2: (⌈x / Δa⌉ - 1) * Δa < (x / Δa) * Δa := by apply (mul_lt_mul_right ha).mpr i1
  have e: (x / Δa) * Δa = x :=by field_simp;
  linarith

lemma k_neg (hx : x < 0) : k Δa x < 0 := by
  have i1 : rb2 Δa x < x := rb2_lt_x _ ha
  have : Φm (ra2 Δa x) < Φm (rb2 Δa x) := by
    apply Φm_strictAnti
    any_goals simp;
    linarith; unfold ra2; linarith; unfold ra2; linarith
  unfold k; linarith

lemma cotrans2 (hx : x < 0) : Φm x = Pestimate2 Δa x :=by
  unfold Pestimate2 Φm
  have i0: (2:ℝ) ^ x < 1 :=by
    apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
  have i1: (2:ℝ) ^ rb2 Δa x < 1 := by
    apply rpow_lt_one_of_one_lt_of_neg one_lt_two
    apply lt_trans _ hx
    apply rb2_lt_x _ ha
  have i2: (2:ℝ) ^ k Δa x < 1 :=by
    apply rpow_lt_one_of_one_lt_of_neg one_lt_two
    apply k_neg _ ha hx
  have i3: (2:ℝ) ^ ra2 Δa x < 1 := by
    have i0 : rb2 Δa x < x := rb2_lt_x _ ha
    apply rpow_lt_one_of_one_lt_of_neg one_lt_two
    unfold ra2; linarith
  have e1: logb 2 (1 - 2 ^ rb2 Δa x) + logb 2 (1 - 2 ^ k Δa x) = logb 2 ((1 - 2 ^ rb2 Δa x) * (1 - 2 ^ k Δa x)) := by
    rw [← logb_mul]; linarith; linarith
  rw[e1]; unfold logb; field_simp;
  apply Real.exp_eq_exp.mp;
  have e: rexp (log (1 - 2 ^ x)) = 1 - 2 ^ x := by apply Real.exp_log; linarith
  rw[e]
  have e: rexp (log ((1 - 2 ^ rb2 Δa x) * (1 - 2 ^ k Δa x)))= (1 - 2 ^ rb2 Δa x) * (1 - 2 ^ k Δa x):= by
    apply Real.exp_log; apply mul_pos; linarith; linarith
  rw[e]
  set a:= (2:ℝ)^ra2 Δa x
  set b:= (2:ℝ)^rb2 Δa x
  have e: 2^ k Δa x = 2^x * (1-(2:ℝ)^ra2 Δa x)/(1-(2:ℝ)^rb2 Δa x) := by
    unfold k Φm; rw [rpow_add, rpow_sub, rpow_logb, rpow_logb]; field_simp;
    any_goals linarith;
  rw[e];
  have e: (1 - b) * (1 - 2 ^ x * (1 - a) / (1 - b)) = 1 - b - 2^x + a* 2^x  := by
    have i: 1 - b ≠ 0 := by linarith;
    field_simp; ring_nf
  rw[e];
  have e: a * (2:ℝ) ^ x = b :=by rw [← rpow_add]; unfold ra2; simp; linarith
  rw[e]; ring_nf


lemma bound_case2 (Φe : FunApprox Φm (Set.Iic (-1))) (hx : x < 0) (hk : k Δa x ≤ -1) (hkr : krnd fix Δa x ≤ -1) :
    |Φm x - Prnd2 fix Δa Φe x| ≤ fix.ε + Φm (-1 - 2 * fix.ε) - Φm (-1) + Φe.err := by
  have e : Φm x = Pestimate2 Δa x := cotrans2 _ ha hx
  rw[e]
  set s1:= Φm (rb2 Δa x) - fix.rnd (Φm (rb2 Δa x) )
  set s2:= Φm (k Δa x) - Φm (krnd fix Δa x)
  set s3:= Φm (krnd fix Δa x) - Φe (krnd fix Δa x)
  have e: Pestimate2 Δa x - Prnd2 fix Δa Φe x = s1 + s2 + s3 := by
    unfold Pestimate2 Prnd2; ring_nf
  rw[e];
  have i01: |s1 + s2 + s3| ≤ |s1 + s2| + |s3|:= by apply abs_add
  have i02: |s1 + s2| ≤ |s1| + |s2|:= by apply abs_add
  have i1 : |s1| ≤ fix.ε := by apply fix.hrnd
  have i3 : |s3| ≤ Φe.err := by
    apply funApprox_err_sym
    apply hkr
  have i2 : |s2| ≤ Φm (-1-2*fix.ε) - Φm (-1) :=by
    apply Lemma71 (by norm_num : -1 < (0 : ℝ)) hk hkr
    set a1:= fix.rnd (Φm (rb2 Δa x) ) - Φm (rb2 Δa x)
    set a2:= Φm (ra2 Δa x) - fix.rnd (Φm (ra2 Δa x))
    have e: k Δa x - krnd fix Δa x = a1 + a2:= by unfold k krnd; ring_nf;
    rw[e]
    have i0: |a1 + a2| ≤ |a1| + |a2|:= by apply abs_add
    have i1 : |a1| ≤ fix.ε := by apply hrndn;
    have i2 : |a2| ≤ fix.ε := by apply fix.hrnd
    linarith
  linarith

-- end Cotrans2

-- /-Case 3-/

-- def rc (x:ℝ) (Δb:ℝ) := (Int.ceil (x/Δb) - 1) * Δb

-- def rab (x:ℝ) (Δb:ℝ) := (rc x Δb) - x

-- def rb (x:ℝ) (Δa:ℝ) (Δb:ℝ) := (Int.ceil ( rab x Δb  /Δa) - 1) * Δa

-- def ra (x:ℝ) (Δa:ℝ) (Δb:ℝ) :=  rb x Δa Δb  - rab x Δb

-- def k1 (x:ℝ) (Δa:ℝ) (Δb:ℝ) := rab x Δb  - Φm (rb x Δa Δb)  + Φm (ra x Δa Δb)

-- def k2 (x:ℝ) (Δa:ℝ) (Δb:ℝ) := x + Φm (rb x Δa Δb) + Φm (k1 x Δa Δb) - Φm (rc x Δb)

-- def Pest3 (x:ℝ) (Δa:ℝ) (Δb:ℝ) := Φm (rc x Δb) +  Φm (k2 x Δa Δb)

-- def k1rnd (x:ℝ) (Δa:ℝ) (Δb:ℝ) := rab x Δb  - fix.rnd (Φm (rb x Δa Δb))  + fix.rnd (Φm (ra x Δa Δb))

-- def k2rnd (x:ℝ) (Δa:ℝ) (Δb:ℝ) := x + fix.rnd (Φm (rb x Δa Δb)) + Φe (k1rnd fix x Δa Δb) - fix.rnd (Φm (rc x Δb))

-- def Prnd3 (x:ℝ) (Δa:ℝ) (Δb:ℝ) := fix.rnd (Φm (rc x Δb)) +  Φe (k2rnd fix x Δa Δb)

-- lemma cotrans3 (hx: x<0) (ha:Δa >0) (hb:Δb >0): Φm x = Pest3 x Δa Δb :=by
--   have e1: Φm x  = Pest2 x Δb := cotrans2 hx hb
--   rw[e1]; unfold Pest2 Pest3
--   have e0: rb2 x Δb = rc x Δb :=by unfold rb2 rc; simp;
--   rw[e0]; simp;
--   have e2: Φm (ra2 x Δb) = Φm (rb x Δa Δb) + Φm (k1 x Δa Δb) :=by
--     apply cotrans2;
--     have i0: rb2 x Δb < x := rb2_lt_x hb;
--     unfold ra2; linarith; assumption
--   have e: k x Δb = k2 x Δa Δb:=by
--     unfold k k2; rw[e0, e2]; ring_nf;
--   rw[e]


-- def Ek2 := 2*fix.ε +  Φm (-1-2*fix.ε) - Φm (-1) + EΦ

-- lemma bound_case3 (hx: x<0) (ha:Δa >0) (hb:Δb >0)
--     (hk1: k1 x Δa Δb ≤ -1) (hk1r: k1rnd fix x Δa Δb ≤ -1)
--     (hk2: k2 x Δa Δb ≤ -1) (hk2r: k2rnd fix x Δa Δb ≤ -1):
--     |Φm x - Prnd3 fix x Δa Δb| ≤ fix.ε +  Φm (-1- Ek2 fix) - Φm (-1) + EΦ :=by
--   have e: Φm x = Pest3 x Δa Δb := cotrans3 hx ha hb
--   rw[e]
--   set s1:= Φm (rc x Δb) - fix.rnd (Φm (rc x Δb) )
--   set s2:= Φm (k2 x Δa Δb) - Φm (k2rnd fix x Δa Δb)
--   set s3:= Φm (k2rnd fix x Δa Δb) - Φe (k2rnd fix x Δa Δb)
--   have e: Pest3 x Δa Δb - Prnd3 fix x Δa Δb = s1 + s2 + s3  :=by unfold Pest3 Prnd3; ring_nf
--   rw[e];
--   have i01: |s1 + s2 + s3| ≤ |s1 + s2| + |s3|:= by apply abs_add
--   have i02: |s1 + s2| ≤ |s1| + |s2|:= by apply abs_add
--   have i1 : |s1| ≤ fix.ε := by apply fix.hrnd
--   have i3 : |s3| ≤ EΦ := by apply hΦen;
--   have i2 : |s2| ≤  Φm (-1- Ek2 fix) - Φm (-1) :=by
--     apply Lemma71 hk2 hk2r
--     set a1:=  Φm (rb x Δa Δb) - fix.rnd (Φm (rb x Δa Δb))
--     set a2:=  fix.rnd (Φm (rc x Δb)) - Φm (rc x Δb)
--     set a3:=   Φm (k1 x Δa Δb) - Φm (k1rnd fix x Δa Δb)
--     set a4:=  Φm (k1rnd fix x Δa Δb) - Φe (k1rnd fix x Δa Δb)
--     have e: k2 x Δa Δb - k2rnd fix x Δa Δb = a1 + a2 + a3 + a4 := by unfold k2 k2rnd; ring_nf;
--     rw[e]
--     have i00: |a1 + a2 + a3 + a4| ≤ |a1 + a2 + a3| + |a4|:= by apply abs_add
--     have i01: |a1 + a2 + a3| ≤ |a1 + a2| + |a3|:= by apply abs_add
--     have i02: |a1 + a2| ≤ |a1| + |a2|:= by apply abs_add
--     have i1 : |a1| ≤ fix.ε := by apply fix.hrnd
--     have i2 : |a2| ≤ fix.ε := by apply hrndn;
--     have i4 : |a4| ≤ EΦ := by apply hΦen;
--     have i3 : |a3| ≤  Φm (-1-2*fix.ε) - Φm (-1) :=by
--       apply Lemma71 hk1 hk1r
--       set b1:= fix.rnd (Φm (rb x Δa Δb)) - Φm (rb x Δa Δb)
--       set b2:= Φm (ra x Δa Δb) - fix.rnd (Φm (ra x Δa Δb))
--       have e: k1 x Δa Δb - k1rnd fix x Δa Δb = b1 + b2 := by unfold k1 k1rnd; ring_nf;
--       rw[e]
--       have i0: |b1 + b2| ≤ |b1| + |b2|:= by apply abs_add
--       have i1 : |b1| ≤ fix.ε := by apply hrndn;
--       have i2 : |b2| ≤ fix.ε := by apply fix.hrnd
--       linarith
--     unfold Ek2; linarith
--   linarith
