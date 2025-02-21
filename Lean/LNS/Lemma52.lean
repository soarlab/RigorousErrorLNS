import LNS.Definitions
import LNS.BasicErrTaylor

open LNS

lemma Lemma52' (hi₀ : i₀ < 0) (hi : i ≤ i₀) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ) : |Em i r| ≤ Em i₀ Δ := by
  have hi0 : i < 0 := by linarith
  rw [abs_of_nonneg (Em_r_nonneg hi0 hr1)]
  have ieq1 := Em_i_monotoneOn hr1 (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio, hi₀]) hi
  have ieq2 : Em i₀ r ≤ Em i₀ Δ := Em_r_monotoneOn hi₀ hr1 (by linarith : 0 ≤ Δ) hr2
  linarith

lemma Lemma52 (hi₀ : i₀ < 0) (hi : i ≤ i₀) (hr1 : 0 ≤ r) (hr2 : r < Δ) : |Em i r| < Em i₀ Δ := by
  have hi0 : i < 0 := by linarith
  rw [abs_of_nonneg (Em_r_nonneg hi0 hr1)]
  have ieq1 := Em_i_monotoneOn hr1 (by simp only [Set.mem_Iio]; linarith) (by simp only [Set.mem_Iio, hi₀]) hi
  have ieq2 : Em i₀ r < Em i₀ Δ := Em_r_strictMonoOn hi₀ hr1 (by linarith : 0 ≤ Δ) hr2
  linarith
