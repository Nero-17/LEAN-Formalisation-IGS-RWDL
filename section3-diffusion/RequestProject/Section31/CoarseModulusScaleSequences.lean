import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Floor.Ring

/-! A deterministic choice of spatial crossing thresholds and time windows.
The grid union factor is included in the limit. These are numerical lemmas,
not a construction or tightness theorem for any stochastic process. -/

namespace IGS.Sec31

open Filter
open scoped Topology
noncomputable section

def coarseModulusCrossings (scale distanceRate : ℝ) (level : ℕ) : ℕ :=
  ⌈scale * distanceRate ^ level⌉₊ + 1

def coarseModulusWindow (scale distanceRate timeRate coefficient : ℝ) (level : ℕ) : ℝ :=
  coefficient * timeRate⁻¹ ^ level * (coarseModulusCrossings scale distanceRate level : ℝ)

theorem coarseModulusCrossings_bounds {scale distanceRate : ℝ}
    (scalePositive : 0 < scale) (ratePositive : 0 < distanceRate) (level : ℕ) :
    1 ≤ (coarseModulusCrossings scale distanceRate level : ℝ) ∧
      scale * distanceRate ^ level ≤ (coarseModulusCrossings scale distanceRate level : ℝ) ∧
      (coarseModulusCrossings scale distanceRate level : ℝ) ≤ scale * distanceRate ^ level + 2 := by
  have nonnegative : 0 ≤ scale * distanceRate ^ level := (mul_pos scalePositive (pow_pos ratePositive level)).le
  have lower := Nat.le_ceil (scale * distanceRate ^ level)
  have upper := Nat.ceil_lt_add_one nonnegative
  simp only [coarseModulusCrossings, Nat.cast_add, Nat.cast_one]
  constructor
  · linarith [show (0 : ℝ) ≤ (⌈scale * distanceRate ^ level⌉₊ : ℝ) from Nat.cast_nonneg _]
  constructor <;> linarith

theorem coarseModulusWindow_positive {scale distanceRate timeRate coefficient : ℝ}
    (scalePositive : 0 < scale) (distancePositive : 0 < distanceRate)
    (timePositive : 0 < timeRate) (coefficientPositive : 0 < coefficient) (level : ℕ) :
    0 < coarseModulusWindow scale distanceRate timeRate coefficient level := by
  have crossingsPositive : 0 < (coarseModulusCrossings scale distanceRate level : ℝ) :=
    lt_of_lt_of_le zero_lt_one (coarseModulusCrossings_bounds scalePositive distancePositive level).1
  exact mul_pos (mul_pos coefficientPositive (pow_pos (inv_pos.mpr timePositive) level)) crossingsPositive

theorem coarseModulusWindow_tendsto_zero {scale distanceRate timeRate coefficient : ℝ}
    (scalePositive : 0 < scale) (rateGeTwo : 2 ≤ distanceRate)
    (timeGeSquare : distanceRate ^ 2 ≤ timeRate) (coefficientPositive : 0 < coefficient) :
    Tendsto (coarseModulusWindow scale distanceRate timeRate coefficient) atTop (𝓝 0) := by
  have distancePositive : 0 < distanceRate := by linarith
  have timeGreaterOne : 1 < timeRate := by nlinarith
  have timePositive : 0 < timeRate := by linarith
  have ratioNonnegative : 0 ≤ distanceRate / timeRate := div_nonneg distancePositive.le timePositive.le
  have ratioLessOne : distanceRate / timeRate < 1 := (div_lt_one timePositive).mpr (by nlinarith)
  have ratioLimit := tendsto_pow_atTop_nhds_zero_of_lt_one ratioNonnegative ratioLessOne
  have inverseLimit := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr timePositive.le)
    ((inv_lt_one₀ timePositive).mpr timeGreaterOne)
  have upperLimit : Tendsto (fun level : ℕ =>
      coefficient * scale * (distanceRate / timeRate) ^ level +
        2 * coefficient * timeRate⁻¹ ^ level) atTop (𝓝 0) := by
    simpa using (ratioLimit.const_mul (coefficient * scale)).add (inverseLimit.const_mul (2 * coefficient))
  apply squeeze_zero (fun level => (coarseModulusWindow_positive scalePositive distancePositive
    timePositive coefficientPositive level).le) _ upperLimit
  intro level
  have upper := (coarseModulusCrossings_bounds scalePositive distancePositive level).2.2
  have scaled := mul_le_mul_of_nonneg_left upper
    (mul_pos coefficientPositive (pow_pos (inv_pos.mpr timePositive) level)).le
  unfold coarseModulusWindow
  convert scaled using 1 <;> simp only [div_pow, div_eq_mul_inv, inv_pow] <;> ring

/-- Exponential growth of the crossing threshold beats every geometric
grid-size factor, regardless of how large the fixed time rate is. -/
theorem geometric_mul_exp_neg_geometric_tendsto_zero {timeRate distanceRate decay : ℝ}
    (timePositive : 0 < timeRate) (distanceGreaterOne : 1 < distanceRate)
    (decayPositive : 0 < decay) :
    Tendsto (fun level : ℕ => timeRate ^ level * Real.exp (-decay * distanceRate ^ level))
      atTop (𝓝 0) := by
  have distancePositive : 0 < distanceRate := zero_lt_one.trans distanceGreaterOne
  have ratioLimit : Tendsto (fun level : ℕ =>
      ((level : ℝ) / distanceRate ^ level) * Real.log timeRate) atTop (𝓝 0) := by
    simpa only [pow_one, zero_mul] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 distanceGreaterOne).mul_const (Real.log timeRate)
  have eventuallySmall : ∀ᶠ level : ℕ in atTop,
      ((level : ℝ) / distanceRate ^ level) * Real.log timeRate < decay / 2 :=
    ratioLimit.eventually (gt_mem_nhds (by linarith))
  have exponentialLimit : Tendsto (fun level : ℕ => Real.exp (-(decay / 2) * distanceRate ^ level))
      atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact (tendsto_pow_atTop_atTop_of_one_lt distanceGreaterOne).const_mul_atTop_of_neg (by linarith)
  apply squeeze_zero' (Eventually.of_forall (fun level => by positivity)) _ exponentialLimit
  filter_upwards [eventuallySmall] with level small
  have exponentSmall : (level : ℝ) * Real.log timeRate < (decay / 2) * distanceRate ^ level := by
    have scaled := (mul_lt_mul_of_pos_right small (pow_pos distancePositive level))
    convert scaled using 1 <;> field_simp [pow_ne_zero level distancePositive.ne']
  calc
    timeRate ^ level * Real.exp (-decay * distanceRate ^ level) =
        Real.exp ((level : ℝ) * Real.log timeRate - decay * distanceRate ^ level) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log timePositive]
      congr 2 <;> ring
    _ ≤ Real.exp (-(decay / 2) * distanceRate ^ level) := Real.exp_le_exp.mpr (by linarith)

theorem coarseModulusGridTail_tendsto_zero {scale distanceRate timeRate coefficient contraction horizon : ℝ}
    (scalePositive : 0 < scale) (rateGeTwo : 2 ≤ distanceRate)
    (timeGeSquare : distanceRate ^ 2 ≤ timeRate)
    (coefficientPositive : 0 < coefficient) (contractionPositive : 0 < contraction)
    (negativeExponent : coefficient + Real.log contraction < 0) (horizonNonnegative : 0 ≤ horizon) :
    Tendsto (fun level : ℕ =>
      (horizon / coarseModulusWindow scale distanceRate timeRate coefficient level + 1) *
        Real.exp (coarseModulusWindow scale distanceRate timeRate coefficient level / timeRate⁻¹ ^ level) *
        contraction ^ coarseModulusCrossings scale distanceRate level) atTop (𝓝 0) := by
  have distancePositive : 0 < distanceRate := by linarith
  have distanceGreaterOne : 1 < distanceRate := by linarith
  have timeGreaterOne : 1 < timeRate := by nlinarith
  have timePositive : 0 < timeRate := by linarith
  have decayPositive : 0 < -(coefficient + Real.log contraction) * scale :=
    mul_pos (neg_pos.mpr negativeExponent) scalePositive
  have upperLimit : Tendsto (fun level : ℕ =>
      (horizon / coefficient + 1) *
        (timeRate ^ level * Real.exp (-(-(coefficient + Real.log contraction) * scale) * distanceRate ^ level)))
      atTop (𝓝 0) := by
    simpa using (geometric_mul_exp_neg_geometric_tendsto_zero timePositive distanceGreaterOne
      decayPositive).const_mul (horizon / coefficient + 1)
  apply squeeze_zero (fun level => by
    have windowPositive := coarseModulusWindow_positive scalePositive distancePositive timePositive coefficientPositive level
    positivity) _ upperLimit
  intro level
  have windowPositive := coarseModulusWindow_positive scalePositive distancePositive timePositive coefficientPositive level
  have crossingsBounds := coarseModulusCrossings_bounds scalePositive distancePositive level
  have timePowerPositive : 0 < timeRate⁻¹ ^ level := pow_pos (inv_pos.mpr timePositive) level
  have timePowerGeOne : 1 ≤ timeRate ^ level := one_le_pow₀ timeGreaterOne.le
  have windowLower : coefficient * timeRate⁻¹ ^ level ≤
      coarseModulusWindow scale distanceRate timeRate coefficient level := by
    unfold coarseModulusWindow
    exact le_mul_of_one_le_right (mul_pos coefficientPositive timePowerPositive).le crossingsBounds.1
  have gridBound : horizon / coarseModulusWindow scale distanceRate timeRate coefficient level + 1 ≤
      (horizon / coefficient + 1) * timeRate ^ level := by
    have divideBound := div_le_div_of_nonneg_left horizonNonnegative
      (mul_pos coefficientPositive timePowerPositive) windowLower
    have cancellation : horizon / (coefficient * timeRate⁻¹ ^ level) = horizon / coefficient * timeRate ^ level := by
      rw [inv_pow]
      field_simp [coefficientPositive.ne', pow_ne_zero level timePositive.ne']
    rw [cancellation] at divideBound
    nlinarith
  have exponentialBound :
      Real.exp (coarseModulusWindow scale distanceRate timeRate coefficient level / timeRate⁻¹ ^ level) *
          contraction ^ coarseModulusCrossings scale distanceRate level ≤
        Real.exp (-(-(coefficient + Real.log contraction) * scale) * distanceRate ^ level) := by
    have cancellation : coarseModulusWindow scale distanceRate timeRate coefficient level / timeRate⁻¹ ^ level =
        coefficient * (coarseModulusCrossings scale distanceRate level : ℝ) := by
      unfold coarseModulusWindow
      field_simp [timePowerPositive.ne']
    rw [cancellation]
    have powerExpression : contraction ^ coarseModulusCrossings scale distanceRate level =
        Real.exp ((coarseModulusCrossings scale distanceRate level : ℝ) * Real.log contraction) := by
      rw [Real.exp_nat_mul, Real.exp_log contractionPositive]
    rw [powerExpression, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have scaled := mul_le_mul_of_nonpos_left crossingsBounds.2.1 negativeExponent.le
    nlinarith
  calc
    _ = (horizon / coarseModulusWindow scale distanceRate timeRate coefficient level + 1) *
        (Real.exp (coarseModulusWindow scale distanceRate timeRate coefficient level / timeRate⁻¹ ^ level) *
          contraction ^ coarseModulusCrossings scale distanceRate level) := by ring
    _ ≤ ((horizon / coefficient + 1) * timeRate ^ level) *
        Real.exp (-(-(coefficient + Real.log contraction) * scale) * distanceRate ^ level) :=
      mul_le_mul gridBound exponentialBound (by positivity) (by positivity)
    _ = _ := by ring

theorem exists_coarseModulusWindows {scale distanceRate timeRate contraction horizon : ℝ}
    (scalePositive : 0 < scale) (rateGeTwo : 2 ≤ distanceRate)
    (timeGeSquare : distanceRate ^ 2 ≤ timeRate)
    (contractionPositive : 0 < contraction) (contractionLessOne : contraction < 1)
    (horizonNonnegative : 0 ≤ horizon) :
    ∃ coefficient : ℝ, 0 < coefficient ∧
      (∀ level, 0 < coarseModulusWindow scale distanceRate timeRate coefficient level) ∧
      Tendsto (coarseModulusWindow scale distanceRate timeRate coefficient) atTop (𝓝 0) ∧
      Tendsto (fun level : ℕ =>
        (horizon / coarseModulusWindow scale distanceRate timeRate coefficient level + 1) *
          Real.exp (coarseModulusWindow scale distanceRate timeRate coefficient level / timeRate⁻¹ ^ level) *
          contraction ^ coarseModulusCrossings scale distanceRate level) atTop (𝓝 0) := by
  have logNegative := Real.log_neg contractionPositive contractionLessOne
  have coefficientPositive : 0 < -(Real.log contraction) / 2 := by linarith
  refine ⟨-(Real.log contraction) / 2, coefficientPositive, ?_,
    coarseModulusWindow_tendsto_zero scalePositive rateGeTwo timeGeSquare coefficientPositive,
    coarseModulusGridTail_tendsto_zero scalePositive rateGeTwo timeGeSquare coefficientPositive
      contractionPositive (by linarith) horizonNonnegative⟩
  intro level
  apply coarseModulusWindow_positive scalePositive (by linarith) _ coefficientPositive level
  nlinarith

end
end IGS.Sec31

#print axioms IGS.Sec31.coarseModulusCrossings_bounds
#print axioms IGS.Sec31.coarseModulusWindow_positive
#print axioms IGS.Sec31.coarseModulusWindow_tendsto_zero
#print axioms IGS.Sec31.geometric_mul_exp_neg_geometric_tendsto_zero
#print axioms IGS.Sec31.coarseModulusGridTail_tendsto_zero
#print axioms IGS.Sec31.exists_coarseModulusWindows
