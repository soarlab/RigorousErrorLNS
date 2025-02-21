import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

attribute [fun_prop] Differentiable.rpow
attribute [fun_prop] Differentiable.exp
attribute [fun_prop] Differentiable.div
attribute [fun_prop] DifferentiableOn.rpow
attribute [fun_prop] DifferentiableOn.exp
attribute [fun_prop] DifferentiableOn.div

attribute [fun_prop] ContinuousOn.div_const
attribute [fun_prop] ContinuousOn.rpow
attribute [fun_prop] ContinuousOn.div

-- TODO: generalize, simplify and add to Mathlib

lemma List.forall_append {α : Type u} (xs ys : List α) (p : α → Prop) :
    (xs ++ ys).Forall p ↔ xs.Forall p ∧ ys.Forall p := by
  repeat rw [List.forall_iff_forall_mem]
  rw [List.forall_mem_append]

/- Derivatives for compositions with a linear transformation -/

lemma DifferentiableAt.comp_linear {a b x : ℝ} {f : ℝ → ℝ} (ha : a ≠ 0) :
    DifferentiableAt ℝ (fun x => f (a * x + b)) x ↔ DifferentiableAt ℝ f (a * x + b) := by
  constructor <;> intro df
  · have : f = (fun x => f (a * x + b)) ∘ (fun x => (x - b) / a) := by
      ext y; congr; field_simp
    rw [this]
    apply DifferentiableAt.comp
    · simp only [add_sub_cancel_right]; field_simp
      exact df
    · simp only [differentiableAt_id', differentiableAt_const, sub, div_const]
  · apply DifferentiableAt.comp
    · exact df
    · simp only [differentiableAt_add_const_iff]
      exact DifferentiableAt.const_mul differentiableAt_id' _

lemma deriv_comp_linear {a b x : ℝ} {f : ℝ → ℝ} :
    deriv (fun x => f (a * x + b)) x = a * deriv f (a * x + b) := by
  by_cases ha : a = 0; simp [ha]
  by_cases df : DifferentiableAt ℝ f (a * x + b)
  · rw [← Function.comp_def, deriv_comp, deriv_add_const, deriv_const_mul, deriv_id'', mul_comm, mul_one]
    · exact differentiableAt_id'
    · exact df
    · apply DifferentiableAt.add_const
      exact DifferentiableAt.const_mul differentiableAt_id' _
  · rw [deriv_zero_of_not_differentiableAt df, deriv_zero_of_not_differentiableAt, mul_zero]
    rw [DifferentiableAt.comp_linear ha]
    exact df

lemma DifferentiableAt.comp_const_sub {a x : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun x => f (a - x)) x ↔ DifferentiableAt ℝ f (a - x) := by
  have : ∀ x, a - x = (-1) * x + a := by intro; ring
  simp only [this, DifferentiableAt.comp_linear (by norm_num : -1 ≠ (0 : ℝ))]

lemma DifferentiableAt.comp_sub_const {a x : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun x => f (x - a)) x ↔ DifferentiableAt ℝ f (x - a) := by
  have : ∀ x, x - a = 1 * x + -a := by intro; ring
  simp only [this, DifferentiableAt.comp_linear (by norm_num : 1 ≠ (0 : ℝ))]

section Diff

open Real

lemma deriv_EqOn_open {f1 f2 : ℝ → ℝ} (hs : IsOpen s) (h : Set.EqOn f1 f2 s) (hx : x ∈ s) :
    deriv f1 x = deriv f2 x := by
  apply Filter.EventuallyEq.deriv_eq
  apply Filter.eventuallyEq_of_mem _ h
  exact IsOpen.mem_nhds hs hx

lemma deriv_EqOn_Iio {f1 f2: ℝ → ℝ} (h: Set.EqOn f1 f2 (Set.Iio (a:ℝ))) (hx: x ∈ Set.Iio (a:ℝ)) :
    deriv f1 x = deriv f2 x := deriv_EqOn_open isOpen_Iio h hx

lemma deriv_EqOn_Ioi {f1 f2: ℝ → ℝ} (h: Set.EqOn f1 f2 (Set.Ioi (a:ℝ))) (hx: x ∈ (Set.Ioi (a:ℝ))) :
    deriv f1 x = deriv f2 x := deriv_EqOn_open isOpen_Ioi h hx

lemma deriv_EqOn_Ioo {f1 f2: ℝ → ℝ} (h: Set.EqOn f1 f2 (Set.Ioo (a:ℝ) (b:ℝ))) (hx: x ∈ (Set.Ioo (a:ℝ) (b:ℝ))) :
    deriv f1 x = deriv f2 x := deriv_EqOn_open isOpen_Ioo h hx

/- Special derivatives -/

-- lemma HasDerivAt.const_rpow {f : ℝ → ℝ} {f' a : ℝ} (ha : 0 < a) (hf : HasDerivAt f f' x) :
--     HasDerivAt (fun x => a ^ f x) (f' * a ^ f x * Real.log a) x := by
--   rw [(by norm_num : f' * a ^ f x * Real.log a = 0 * f x * a ^ (f x - 1) + f' * a ^ f x * Real.log a)]
--   exact HasDerivAt.rpow (hasDerivAt_const x a) hf ha

lemma HasDerivAt.const_rpow {f : ℝ → ℝ} {f' a : ℝ} (ha : 0 < a) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => a ^ f x) ((Real.log a * f') * a ^ f x) x := by
  rw [(by norm_num; ring : (Real.log a * f') * a ^ f x = 0 * f x * a ^ (f x - 1) + f' * a ^ f x * Real.log a)]
  exact HasDerivAt.rpow (hasDerivAt_const x a) hf ha

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E} {f' : E →L[ℝ] ℝ}
  {s : Set E}

theorem DifferentiableWithinAt.logb (b : ℝ) (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun x => logb b (f x)) s x := by
  unfold Real.logb
  fun_prop (disch := assumption)

@[fun_prop]
theorem DifferentiableAt.logb (b : ℝ) (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    DifferentiableAt ℝ (fun x => logb b (f x)) x := by
  unfold Real.logb
  fun_prop (disch := assumption)

@[fun_prop]
theorem DifferentiableOn.logb (b : ℝ) (hf : DifferentiableOn ℝ f s) (hx : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun x => logb b (f x)) s := fun x h => (hf x h).logb b (hx _ h)

theorem Differentiable.logb (hf : Differentiable ℝ f) (hx : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun x => logb b (f x) := fun x => (hf x).logb b (hx x)

end Diff

/- Some special limits -/

section Limits

open Real Filter Topology

lemma tendsto_x_mul_inv_x : Tendsto (fun x : ℝ => x * x⁻¹) (𝓝[≠] 0) (𝓝 1) := by
  field_simp; apply tendsto_nhds_of_eventually_eq; apply eventually_nhdsWithin_of_forall
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro x hx
  field_simp

-- Adapted from this proof: https://github.com/leanprover-community/mathlib4/blob/052d8d57c394373282ac1b581e828d9f3625e94c/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean#L208-L215
lemma tendsto_log_mul_inv_x (a : ℝ) : Tendsto (fun x : ℝ => log (a * x + 1) * x⁻¹) (𝓝[≠] 0) (𝓝 a) := by
  simpa [mul_comm, hasDerivAt_iff_tendsto_slope, slope_fun_def] using
     (((hasDerivAt_id (0 : ℝ)).const_mul a).add_const 1).log (by norm_num)

end Limits

/- Monotonicity of restricted function -/

lemma monotone_restrict [Preorder α] [Preorder β] {f : α → β} {s : Set α} :
    Monotone (s.restrict f) ↔ MonotoneOn f s := by simp [Set.restrict, Monotone, MonotoneOn]

lemma antitone_restrict [Preorder α] [Preorder β] {f : α → β} {s : Set α} :
    Antitone (s.restrict f) ↔ AntitoneOn f s := by simp [Set.restrict, Antitone, AntitoneOn]

/- Int.ceil lemmas -/

namespace Int

variable {F α β : Type*}
variable [LinearOrderedRing α] [FloorRing α] {z : ℤ} {a : α}

lemma ceil_nonpos (ha : a ≤ 0) : ⌈a⌉ ≤ 0 := by
  rw [ceil_le, cast_zero]; exact ha

lemma floor_eq_self : ↑⌊a⌋ = a ↔ fract a = 0 := by
  simp only [fract, sub_eq_zero, eq_comm]

lemma ceil_eq_floor_iff_frac_eq_zero : ⌈a⌉ = ⌊a⌋ ↔ fract a = 0 := by
  constructor <;> intro h
  · exact le_antisymm (sub_nonpos_of_le $ h ▸ le_ceil _) (fract_nonneg a)
  · rw [ceil_eq_iff, floor_eq_self.mpr h]
    exact ⟨sub_one_lt _, le_refl _⟩

lemma ceil_eq_self : ↑⌈a⌉ = a ↔ fract a = 0 := by
  constructor <;> intro h
  · rw [← ceil_eq_floor_iff_frac_eq_zero]
    apply le_antisymm _ (floor_le_ceil a)
    rw [← @Int.cast_le α, h, ←h, floor_intCast]
  · rw [ceil_eq_floor_iff_frac_eq_zero.mpr h, floor_eq_self.mpr h]

section LinearOrderedField

variable {k : Type*} [LinearOrderedField k] [FloorRing k] {b : k}

lemma ceil_div_mul_sub_lt {a b : k} (hb : 0 < b) : ⌈a / b⌉ * b - a < b := by
  rw [sub_lt_iff_lt_add, ←lt_div_iff₀ hb, same_add_div (ne_of_gt hb), add_comm]
  exact ceil_lt_add_one _

lemma ceil_div_mul_sub_nonneg {a b : k} (hb : 0 < b) : 0 ≤ ⌈a / b⌉ * b - a := by
  rw [sub_nonneg, ← div_le_iff₀ hb]
  exact le_ceil _

end LinearOrderedField

end Int
