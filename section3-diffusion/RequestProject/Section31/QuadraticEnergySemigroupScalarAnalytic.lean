import RequestProject.Section31.QuadraticEnergyYosidaDerivativeBound
import RequestProject.Section31.BoundedSemigroupScalarSeries
import RequestProject.Section31.ScalarPowerSeriesLimit
import RequestProject.Section31.QuadraticEnergySemigroup

/-! Scalar time analyticity of the actually constructed closed semigroup.
The actual self-adjoint nonnegative Yosida generators supply the centered
series and its uniform geometric coefficient bound. Their proved strong limit
supplies convergence. No semigroup analyticity or spectral representation is
assumed. The real-time expression uses toNNReal only to define it outside the
positive interval; its analyticity conclusion is strictly at positive times.
Candidate source, awaiting whole-file compilation. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable local instance : NormedAlgebra ℚ (H →L[ℝ] H) :=
  NormedAlgebra.restrictScalars ℚ ℝ (H →L[ℝ] H)

theorem closedSemigroup_scalar_analyticAt
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H)) (first second : H)
    (time : ℝ) (timePositive : 0 < time) :
    AnalyticAt ℝ (fun parameter : ℝ =>
      inner ℝ first (closedSemigroup domain form nonnegative closable domainDense parameter.toNNReal second)) time := by
  let generators : ℕ → H →L[ℝ] H := fun index =>
    yosidaGenerator domain form nonnegative closable domainDense (canonicalYosidaStep index)
      (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
  let coefficients : ℕ → ℕ → ℝ := fun index power =>
    (-1 : ℝ) ^ power *
      inner ℝ first ((generators index ^ power * NormedSpace.exp ((-time) • generators index)) second) /
        (power.factorial : ℝ)
  let approximations : ℕ → ℝ → ℝ := fun index increment =>
    inner ℝ first (NormedSpace.exp ((-(time + increment)) • generators index) second)
  let target : ℝ → ℝ := fun parameter =>
    inner ℝ first (closedSemigroup domain form nonnegative closable domainDense parameter.toNNReal second)
  have generatorsSelfAdjoint (index : ℕ) : IsSelfAdjoint (generators index) :=
    yosidaGenerator_selfAdjoint domain form nonnegative closable domainDense (canonicalYosidaStep index)
      (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
  have generatorsNonnegative (index : ℕ) : ∀ values, 0 ≤ inner ℝ (generators index values) values :=
    yosidaGenerator_pairing_nonnegative domain form nonnegative closable domainDense (canonicalYosidaStep index)
      (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)
  change AnalyticAt ℝ target time
  apply scalar_series_pointwise_limit_analyticAt coefficients approximations target time
    (‖first‖ * ‖second‖) (Real.exp 1 / time)
    (mul_nonneg (norm_nonneg first) (norm_nonneg second)) (div_pos (Real.exp_pos _) timePositive)
  · intro index power
    exact BoundedSemigroupEnergy.generator_scalar_coefficient_bound (generators index)
      (generatorsSelfAdjoint index) (generatorsNonnegative index) first second time timePositive power
  · intro index increment
    exact BoundedSemigroupEnergy.bounded_generator_scalar_centered_series
      (generators index) first second time increment
  · intro increment incrementBound
    have exponentialGreaterThanOne : (1 : ℝ) < Real.exp 1 :=
      Real.one_lt_exp_iff.mpr (by norm_num)
    have radiusLessThanTime : (Real.exp 1 / time)⁻¹ < time := by
      rw [inv_div]
      apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
      nlinarith
    have nearbyPositive : 0 < time + increment := by
      have lowerBound := (abs_lt.mp incrementBound).1
      linarith
    have scalarConvergence := (innerSL ℝ first).continuous.continuousAt.tendsto.comp
      (closedSemigroup_approximation_limit domain form nonnegative closable domainDense
        (time + increment).toNNReal second)
    have approximationEquality :
        (fun index => inner ℝ first
          (closedSemigroupApproximation domain form nonnegative closable domainDense index
            (time + increment).toNNReal second)) =
          (fun index => approximations index increment) := by
      funext index
      simp only [closedSemigroupApproximation, yosidaSemigroup_eq_exp,
        Real.coe_toNNReal _ nearbyPositive.le, approximations, generators]
    change Tendsto (fun index => inner ℝ first
      (closedSemigroupApproximation domain form nonnegative closable domainDense index
        (time + increment).toNNReal second)) atTop (𝓝 (target (time + increment))) at scalarConvergence
    rw [approximationEquality] at scalarConvergence
    exact scalarConvergence

theorem closedSemigroup_scalar_analyticOnNhd
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H)) (first second : H) :
    AnalyticOnNhd ℝ (fun parameter : ℝ =>
      inner ℝ first (closedSemigroup domain form nonnegative closable domainDense parameter.toNNReal second))
      (Set.Ioi 0) := by
  intro time timePositive
  exact closedSemigroup_scalar_analyticAt domain form nonnegative closable domainDense first second time timePositive

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_scalar_analyticAt
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_scalar_analyticOnNhd
