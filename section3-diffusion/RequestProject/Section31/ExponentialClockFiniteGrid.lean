import RequestProject.Section31.ExponentialClockWindowBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology

def clockFiniteGridTime (grid index : ℕ) : ℝ :=
  index / (grid + 1 : ℝ)

def clockFiniteGridBad (acceleration : ℝ) (horizon grid : ℕ)
    (tolerance : ℝ) : Set (ℕ → ℝ) :=
  {holdingTimes | ∃ index : Fin ((horizon + 1) * (grid + 1) + 1),
    tolerance ≤ |(holdingJumpIndex holdingTimes
      (acceleration * clockFiniteGridTime grid index.val) : ℝ) /
        acceleration - clockFiniteGridTime grid index.val|}

theorem clockFiniteGridBad_measurable
    (acceleration : ℝ) (horizon grid : ℕ) (tolerance : ℝ) :
    MeasurableSet (clockFiniteGridBad acceleration horizon grid tolerance) := by
  unfold clockFiniteGridBad
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro index
  have jumpMeasurable : Measurable (fun holdingTimes =>
      (holdingJumpIndex holdingTimes (acceleration * clockFiniteGridTime grid index.val) : ℝ)) :=
    (measurable_of_countable (fun count : ℕ => (count : ℝ))).comp (holdingJumpIndex_measurable _)
  exact measurableSet_le measurable_const
    (continuous_abs.measurable.comp ((jumpMeasurable.div_const acceleration).sub
      (measurable_const (a := clockFiniteGridTime grid index.val))))

theorem clockFiniteGridTime_bounds (horizon grid : ℕ)
    (index : Fin ((horizon + 1) * (grid + 1) + 1)) :
    0 ≤ clockFiniteGridTime grid index.val ∧
      clockFiniteGridTime grid index.val ≤ (horizon + 1 : ℕ) := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < grid + 1)).mpr
    have bound : index.val ≤ (horizon + 1) * (grid + 1) := Nat.le_of_lt_succ index.isLt
    exact_mod_cast bound

/-- This clock error event is finite and genuinely Borel measurable.
Its probability tends to zero for the true exponential clock, using the
single universal almost-sure inverse-clock limit already proved. -/
theorem exponential_clock_finite_grid_bad_probability
    (acceleration : ℕ → ℝ) (accelerationPositive : ∀ depth, 0 < acceleration depth)
    (diverge : Tendsto acceleration atTop atTop) (horizon grid : ℕ)
    (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    Tendsto (fun depth => exponentialHoldingTimeLaw.real
      (clockFiniteGridBad (acceleration depth) horizon grid tolerance))
      atTop (𝓝 0) := by
  let bad := fun depth => clockFiniteGridBad (acceleration depth) horizon grid tolerance
  have badMeasurable (depth : ℕ) : MeasurableSet (bad depth) :=
    clockFiniteGridBad_measurable _ _ _ _
  have eventuallyGood : ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
      ∀ᶠ depth in atTop, holdingTimes ∉ bad depth := by
    filter_upwards [exponentialHoldingTimeLaw_jump_clock_uniform] with holdingTimes uniform
    filter_upwards [uniform acceleration accelerationPositive diverge (horizon + 1 : ℕ)
      (Nat.cast_nonneg _) tolerance tolerancePositive] with depth errors
    rintro ⟨index, badError⟩
    have bounds := clockFiniteGridTime_bounds horizon grid index
    exact not_le_of_gt (errors _ bounds.1 bounds.2) badError
  have sampleConverges : ∀ᵐ holdingTimes ∂exponentialHoldingTimeLaw,
      Tendsto (fun depth => (bad depth).indicator (fun _ : ℕ → ℝ => (1 : ℝ)) holdingTimes) atTop (𝓝 0) := by
    filter_upwards [eventuallyGood] with holdingTimes good
    apply tendsto_const_nhds.congr'
    filter_upwards [good] with depth outside
    exact (Set.indicator_of_notMem outside (fun _ : ℕ → ℝ => (1 : ℝ))).symm
  have dominated := tendsto_integral_of_dominated_convergence (μ := exponentialHoldingTimeLaw)
    (F := fun depth => (bad depth).indicator (fun _ : ℕ → ℝ => (1 : ℝ))) (f := fun _ => (0 : ℝ))
    (fun _ : ℕ → ℝ => (1 : ℝ))
    (fun depth => (measurable_const.indicator (badMeasurable depth)).aestronglyMeasurable)
    (integrable_const (1 : ℝ))
    (fun depth => Eventually.of_forall (fun holdingTimes => by
      change ‖(bad depth).indicator (fun _ : ℕ → ℝ => (1 : ℝ)) holdingTimes‖ ≤ (1 : ℝ)
      by_cases belongs : holdingTimes ∈ bad depth
      · simp [belongs]
      · simp [belongs]))
    sampleConverges
  simpa only [integral_indicator_const (1 : ℝ) (badMeasurable _),
    smul_eq_mul, mul_one, integral_zero, bad] using dominated

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.clockFiniteGridBad_measurable
#print axioms IGS.Sec31.PoissonClock.exponential_clock_finite_grid_bad_probability

