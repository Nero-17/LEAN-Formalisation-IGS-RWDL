import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A fixed coarse buffer fits a constant-multiple fine-scale ball inside
the coarse cell-separation radius. The volume conversion loses only a
fixed mass-rate power and does not increase the logarithmic degree cost.
Candidate source: no compilation is claimed. -/

namespace IGS.Sec31
open Filter
open scoped Topology
noncomputable section

theorem exists_fixed_geometric_buffer (rate outerFactor spatialFraction : ℝ)
    (rateGreaterThanOne : 1 < rate) (spatialFractionPositive : 0 < spatialFraction) :
    ∃ buffer : ℕ, outerFactor * rate⁻¹ ^ buffer < spatialFraction := by
  have ratePositive := zero_lt_one.trans rateGreaterThanOne
  have vanishing : Tendsto (fun buffer : ℕ => outerFactor * rate⁻¹ ^ buffer)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr ratePositive.le)
        ((inv_lt_one₀ ratePositive).mpr rateGreaterThanOne)).const_mul outerFactor
  exact (vanishing.eventually (gt_mem_nhds spatialFractionPositive)).exists

theorem geometric_radius_fit_of_fixed_buffer (rate outerFactor spatialFraction : ℝ)
    (ratePositive : 0 < rate) (buffer fine : ℕ) (bufferAtMostFine : buffer ≤ fine)
    (bufferFit : outerFactor * rate⁻¹ ^ buffer < spatialFraction) :
    outerFactor * rate⁻¹ ^ fine < spatialFraction * rate⁻¹ ^ (fine - buffer) := by
  have finePower : rate⁻¹ ^ fine = rate⁻¹ ^ buffer * rate⁻¹ ^ (fine - buffer) := by
    rw [← pow_add, Nat.add_sub_of_le bufferAtMostFine]
  rw [finePower, ← mul_assoc]
  exact mul_lt_mul_of_pos_right bufferFit (pow_pos (inv_pos.mpr ratePositive) (fine - buffer))

theorem logarithmic_degree_cost_mono (degreeRate width : ℝ)
    (degreeAtLeastOne : 1 ≤ degreeRate) (widthNonnegative : 0 ≤ width)
    (coarse fine : ℕ) (ordered : coarse ≤ fine) :
    degreeRate ^ Nat.ceil (width * Real.log (coarse + 2 : ℝ)) ≤
      degreeRate ^ Nat.ceil (width * Real.log (fine + 2 : ℝ)) := by
  have baseOrder : (coarse + 2 : ℝ) ≤ (fine + 2 : ℝ) := by exact_mod_cast Nat.add_le_add_right ordered 2
  have logarithmOrder := Real.log_le_log (by positivity : 0 < (coarse + 2 : ℝ)) baseOrder
  exact pow_le_pow_right₀ degreeAtLeastOne
    (Nat.ceil_mono (mul_le_mul_of_nonneg_left logarithmOrder widthNonnegative))

theorem shifted_logarithmic_geometric_volume_bound
    (massRate degreeRate width coefficient volume : ℝ)
    (massPositive : 0 < massRate) (degreeAtLeastOne : 1 ≤ degreeRate)
    (widthNonnegative : 0 ≤ width) (coefficientNonnegative : 0 ≤ coefficient)
    (buffer fine : ℕ) (bufferAtMostFine : buffer ≤ fine)
    (volumeBound : volume ≤ coefficient *
      degreeRate ^ Nat.ceil (width * Real.log ((fine - buffer : ℕ) + 2 : ℝ)) / massRate ^ (fine - buffer)) :
    volume ≤ (coefficient * massRate ^ buffer) *
      degreeRate ^ Nat.ceil (width * Real.log (fine + 2 : ℝ)) / massRate ^ fine := by
  have degreeBound := logarithmic_degree_cost_mono degreeRate width degreeAtLeastOne widthNonnegative
    (fine - buffer) fine (Nat.sub_le _ _)
  have massPower : massRate ^ fine = massRate ^ (fine - buffer) * massRate ^ buffer := by
    rw [← pow_add, Nat.sub_add_cancel bufferAtMostFine]
  calc
    volume ≤ coefficient * degreeRate ^ Nat.ceil (width * Real.log ((fine - buffer : ℕ) + 2 : ℝ)) /
        massRate ^ (fine - buffer) := volumeBound
    _ ≤ coefficient * degreeRate ^ Nat.ceil (width * Real.log (fine + 2 : ℝ)) /
        massRate ^ (fine - buffer) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left degreeBound coefficientNonnegative)
        (pow_nonneg massPositive.le _)
    _ = _ := by
      rw [massPower]
      field_simp [massPositive.ne']
      <;> ring

end
end IGS.Sec31

#print axioms IGS.Sec31.exists_fixed_geometric_buffer
#print axioms IGS.Sec31.geometric_radius_fit_of_fixed_buffer
#print axioms IGS.Sec31.logarithmic_degree_cost_mono
#print axioms IGS.Sec31.shifted_logarithmic_geometric_volume_bound
