import LNS.Common
import LNS.Tactic
import LNS.Basic
import LNS.Lemma51
import LNS.Lemma52

open LNS


lemma Theorem53_Ep (fix : FixedPoint) {i r Δ : ℝ} (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ) :  |Ep_fix fix i r| ≤ (Ep 0 Δ) + (2+Δ)*fix.ε :=by
  set s1 := (Φp i -  fix.rnd (Φp i))
  set s2 := r*(fix.rnd (deriv Φp i) - deriv Φp i)
  set s3 := (fix.rnd (r * fix.rnd (deriv Φp i)) - r * fix.rnd (deriv Φp i))
  have e1: Ep_fix fix i r = Ep i r + s1 + s2 + s3 := by unfold Ep_fix Ep; ring_nf
  have i1: |s1| ≤ fix.ε := by apply fix.hrnd
  have i3: |s3| ≤ fix.ε := by
    have : |s3| = |r * fix.rnd (deriv Φp i) - fix.rnd (r * fix.rnd (deriv Φp i))| :=by apply abs_sub_comm;
    rw[this]
    apply fix.hrnd
  have i2: |s2| ≤ Δ*fix.ε :=by
    have e1: |s2| = |r| * |(fix.rnd (deriv Φp i) - deriv Φp i)| :=by apply abs_mul
    have e2: |(fix.rnd (deriv Φp i) - deriv Φp i)| = |(deriv Φp i) - fix.rnd (deriv Φp i)|:= by apply abs_sub_comm;
    have e3: |r| = r :=by apply abs_of_nonneg; linarith
    rw[e1,e2,e3]
    have i21: |deriv Φp i - fix.rnd (deriv Φp i)| ≤ fix.ε := by apply fix.hrnd
    apply mul_le_mul hr2 i21; simp; linarith
  have i0: |Ep_fix fix i r| ≤ |Ep i r| + |s1| + |s2| + |s3| :=by
    have i01 : |Ep_fix fix i r| ≤ |Ep i r + s1 + s2| + |s3|:=by rw[e1]; apply abs_add
    have i02 :  |Ep i r + s1 + s2|  ≤    |Ep i r + s1| + |s2|:=by  apply abs_add
    have i03: |Ep i r + s1|  ≤ |Ep i r| + |s1| :=by  apply abs_add
    linarith
  have i01: |Ep i r|≤ Ep 0 Δ :=by exact Lemma51 hi hr1 hr2
  linarith

lemma Theorem53_Em (fix : FixedPoint) {i r Δ : ℝ} (hi : i ≤ -1) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ) : |Em_fix fix i r| ≤ (Em (-1:ℝ) Δ) + (2+Δ)*fix.ε :=by
  set s1 := (Φm i -  fix.rnd (Φm i))
  set s2 := r*(fix.rnd (deriv Φm i) - deriv Φm i)
  set s3 := (fix.rnd (r * fix.rnd (deriv Φm i)) - r * fix.rnd (deriv Φm i))
  have e1: Em_fix fix i r = (-Em i r) + s1 + s2 + s3 := by unfold Em_fix Em; ring_nf
  have i1: |s1| ≤ fix.ε := by apply fix.hrnd
  have i3: |s3| ≤ fix.ε := by
    have : |s3| = |r * fix.rnd (deriv Φm i) - fix.rnd (r * fix.rnd (deriv Φm i))| :=by apply abs_sub_comm;
    rw[this]
    apply fix.hrnd
  have i2: |s2| ≤ Δ*fix.ε :=by
    have e1: |s2| = |r| * |(fix.rnd (deriv Φm i) - deriv Φm i)| :=by apply abs_mul
    have e2: |(fix.rnd (deriv Φm i) - deriv Φm i)| = |(deriv Φm i) - fix.rnd (deriv Φm i)|:= by apply abs_sub_comm;
    have e3: |r| = r :=by apply abs_of_nonneg; linarith
    rw[e1,e2,e3]
    have i21: |deriv Φm i - fix.rnd (deriv Φm i)| ≤ fix.ε := by apply fix.hrnd
    apply mul_le_mul hr2 i21; simp; linarith
  have i0:  |Em_fix fix i r| ≤ |Em i r| + |s1| + |s2| + |s3| :=by
    have i01 : |Em_fix fix i r| ≤ |-Em i r + s1 + s2| + |s3|:=by rw[e1]; apply abs_add
    have i02 :  |-Em i r + s1 + s2|  ≤    |-Em i r + s1| + |s2|:=by  apply abs_add
    have i03: |-Em i r + s1|  ≤ |-Em i r| + |s1| :=by  apply abs_add
    have i04: |-Em i r| =|Em i r|:=by apply abs_neg
    linarith
  have i01: |Em i r|≤ Em (-1:ℝ) Δ :=by exact Lemma52 hi hr1 hr2
  linarith
