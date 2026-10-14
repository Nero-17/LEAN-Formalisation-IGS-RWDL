import RequestProject.Section31.PositiveL2OperatorSupport

/-! A zero nonnegative scalar correlation propagates backwards in time.
Quadratic strict positivity is only an intermediate generic property; the
closed-form consumer fills it using the separately proved self-adjoint C0
semigroup injectivity argument.
Candidate source, awaiting whole-file compilation. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped NNReal

variable {Space : Type*} [MeasurableSpace Space] (law : Measure Space)

theorem positive_L2_semigroup_zero_correlation_of_le
    (semigroup : ℝ≥0 → Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law)
    (addition : ∀ firstTime secondTime,
      semigroup (firstTime + secondTime) = (semigroup firstTime).comp (semigroup secondTime))
    (positive : ∀ time (values : Lp ℝ 2 law),
      (∀ᵐ point ∂law, 0 ≤ values point) → ∀ᵐ point ∂law, 0 ≤ semigroup time values point)
    (strictPairing : ∀ time (values : Lp ℝ 2 law), values ≠ 0 →
      0 < inner ℝ values (semigroup time values))
    (first second : Lp ℝ 2 law)
    (firstNonnegative : ∀ᵐ point ∂law, 0 ≤ first point)
    (secondNonnegative : ∀ᵐ point ∂law, 0 ≤ second point)
    (earlier later : ℝ≥0) (ordered : earlier ≤ later)
    (zero : inner ℝ first (semigroup later second) = 0) :
    inner ℝ first (semigroup earlier second) = 0 := by
  have productZero := (L2_inner_eq_zero_iff_product_ae_zero law first (semigroup later second)
    firstNonnegative (positive later second secondNonnegative)).mp zero
  have zeroInclusion := positive_L2_operator_zero_set_inclusion law (semigroup (later - earlier))
    (positive (later - earlier)) (strictPairing (later - earlier)) (semigroup earlier second)
    (positive earlier second secondNonnegative)
  have outputEquality : semigroup (later - earlier) (semigroup earlier second) = semigroup later second := by
    rw [← ContinuousLinearMap.comp_apply, ← addition, tsub_add_cancel_of_le ordered]
  simp only [outputEquality] at zeroInclusion
  apply (L2_inner_eq_zero_iff_product_ae_zero law first (semigroup earlier second)
    firstNonnegative (positive earlier second secondNonnegative)).mpr
  filter_upwards [productZero, zeroInclusion] with point product zeroBackwards
  by_cases firstZero : first point = 0
  · simp only [firstZero, zero_mul]
  · have laterZero : semigroup later second point = 0 := (mul_eq_zero.mp product).resolve_left firstZero
    rw [zeroBackwards laterZero, mul_zero]

end IGS.Sec31

#print axioms IGS.Sec31.positive_L2_semigroup_zero_correlation_of_le
