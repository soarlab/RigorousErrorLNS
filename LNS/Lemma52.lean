import LNS.Common
import LNS.Tactic
import LNS.Basic

open LNS

lemma Lemma52 (hi₀ : i₀ < 0) (hi : i ≤ i₀) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ) : |Em i r| ≤ Em i₀ Δ := by
  have hi0: i < 0 := by linarith
  rw [abs_of_nonneg (Em_r_nonneg hi0 hr1)]
  have ieq1:= Em_i_monotone hr1 (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio, hi₀]) hi
  simp only [Em_i] at ieq1
  have ieq2: Em i₀ r ≤ Em i₀ Δ := by
    apply StrictMonoOn.monotoneOn (Em_r_strictMonotone _)
    simp only [Set.mem_Ici, hr1]
    simp only [Set.mem_Ici]; linarith
    exact hr2
    simp only [Set.mem_Iio, hi₀]
  linarith
