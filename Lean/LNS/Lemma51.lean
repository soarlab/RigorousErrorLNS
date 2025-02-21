import LNS.Definitions
import LNS.BasicErrTaylor

namespace LNS

lemma Lemma51' (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ) : |Ep i r| ≤ Ep 0 Δ := by
  rw [abs_of_nonneg (Ep_r_nonneg hr1)]
  have ieq1 := Ep_i_monotoneOn hr1 hi Set.right_mem_Iic hi
  have ieq2 : Ep 0 r ≤ Ep 0 Δ := Ep_r_monotoneOn hr1 (by linarith : 0 ≤ Δ) hr2
  linarith

lemma Lemma51 (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) : |Ep i r| < Ep 0 Δ := by
  rw [abs_of_nonneg (Ep_r_nonneg hr1)]
  have ieq1 := Ep_i_monotoneOn hr1 hi Set.right_mem_Iic hi
  have ieq2 : Ep 0 r < Ep 0 Δ := Ep_r_strictMonoOn hr1 (by linarith : 0 ≤ Δ) hr2
  linarith
