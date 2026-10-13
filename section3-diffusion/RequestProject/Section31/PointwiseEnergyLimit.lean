import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-! A two-scale estimate forces point values to vanish. The coefficient of the
L² term is allowed to depend on the fixed scale; no uniform bound on it is used.
The concrete incidence and projection estimates are supplied separately. -/

namespace IGS.Sec31

open Filter Topology

theorem tendsto_zero_of_two_scale_bounds
    (values norms coefficients errors : ℕ → ℝ)
    (valuesNonnegative : ∀ index, 0 ≤ values index)
    (normsTendsto : Tendsto norms atTop (nhds 0))
    (errorsTendsto : Tendsto errors atTop (nhds 0))
    (bounds : ∀ scale index, values index ≤ coefficients scale * norms index + errors scale) :
    Tendsto values atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro tolerance tolerancePositive
  have smallError : ∀ᶠ scale in atTop, errors scale < tolerance / 2 :=
    errorsTendsto.eventually (gt_mem_nhds (half_pos tolerancePositive))
  obtain ⟨scale, scaleSmall⟩ := smallError.exists
  have firstTendsto : Tendsto (fun index => coefficients scale * norms index) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul normsTendsto
  have smallFirst : ∀ᶠ index in atTop, coefficients scale * norms index < tolerance / 2 :=
    firstTendsto.eventually (gt_mem_nhds (half_pos tolerancePositive))
  obtain ⟨threshold, afterThreshold⟩ := eventually_atTop.1 smallFirst
  refine ⟨threshold, ?_⟩
  intro index indexAfter
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (valuesNonnegative index)]
  exact (bounds scale index).trans_lt (by linarith [afterThreshold index indexAfter])

theorem tendsto_zero_of_two_scale_energy_bounds
    (values norms energies coefficients errors : ℕ → ℝ)
    (energyBound : ℝ) (energiesBounded : ∀ index, energies index ≤ energyBound)
    (errorsNonnegative : ∀ scale, 0 ≤ errors scale)
    (normsTendsto : Tendsto norms atTop (nhds 0))
    (errorsTendsto : Tendsto errors atTop (nhds 0))
    (bounds : ∀ scale index,
      (values index) ^ 2 ≤ coefficients scale * (norms index) ^ 2 + errors scale * energies index) :
    Tendsto values atTop (nhds 0) := by
  have squaresTendsto : Tendsto (fun index => (values index) ^ 2) atTop (nhds 0) := by
    apply tendsto_zero_of_two_scale_bounds (fun index => (values index) ^ 2)
      (fun index => (norms index) ^ 2) coefficients (fun scale => errors scale * energyBound)
      (fun index => sq_nonneg (values index))
    · simpa using normsTendsto.pow 2
    · simpa only [zero_mul] using errorsTendsto.mul_const energyBound
    · intro scale index
      exact (bounds scale index).trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (energiesBounded index) (errorsNonnegative scale)))
  have absoluteTendsto : Tendsto (fun index => |values index|) atTop (nhds 0) := by
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using squaresTendsto.sqrt
  exact (tendsto_zero_iff_norm_tendsto_zero).2 (by simpa only [Real.norm_eq_abs] using absoluteTendsto)

end IGS.Sec31

#print axioms IGS.Sec31.tendsto_zero_of_two_scale_bounds
#print axioms IGS.Sec31.tendsto_zero_of_two_scale_energy_bounds
