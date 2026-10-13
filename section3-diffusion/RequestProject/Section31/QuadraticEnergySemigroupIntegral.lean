import RequestProject.Section31.QuadraticEnergySemigroup
import RequestProject.Section31.BoundedSemigroupIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual Yosida limit solves the closed-operator integral equation on
the actual operator domain. Consequently its right derivative at zero is
minus that closed operator. No generator identification is assumed. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology MeasureTheory
open scoped NNReal

set_option maxHeartbeats 2000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))

theorem closedSemigroupApproximation_generator_limit (time : ℝ≥0)
    (values : generatorDomain domain form nonnegative closable) :
    Tendsto (fun index =>
      closedSemigroupApproximation domain form nonnegative closable domainDense index time
        (yosidaGenerator domain form nonnegative closable domainDense (canonicalYosidaStep index)
          (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) values))
      atTop (nhds (closedSemigroup domain form nonnegative closable domainDense time
        (closedGenerator domain form nonnegative closable domainDense values))) := by
  exact StrongContractionSemigroupLimit.tendsto_varying_apply
    (closedSemigroupApproximation domain form nonnegative closable domainDense)
    (closedSemigroupApproximation_norm domain form nonnegative closable domainDense)
    (closedSemigroupApproximation_cauchy domain form nonnegative closable domainDense) time _ _
    (yosidaGenerator_on_domain_limit domain form nonnegative closable domainDense
      canonicalYosidaStep canonicalYosidaStep_positive canonicalYosidaStep_le_one
      canonicalYosidaStep_tendsto values)

theorem yosidaSemigroup_generator_norm_bound (index : ℕ) (time : ℝ)
    (timeNonnegative : 0 ≤ time) (values : generatorDomain domain form nonnegative closable) :
    ‖yosidaSemigroup domain form nonnegative closable domainDense (canonicalYosidaStep index)
        (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) time
      (yosidaGenerator domain form nonnegative closable domainDense (canonicalYosidaStep index)
        (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) values)‖ ≤
      ‖closedGenerator domain form nonnegative closable domainDense values‖ := by
  apply le_trans (yosidaSemigroup_apply_norm domain form nonnegative closable domainDense
    _ _ _ time timeNonnegative _)
  rw [yosidaGenerator_on_domain]
  exact smallStepResolvent_norm domain form nonnegative closable domainDense _ _ _ _

theorem closedSemigroup_orbit_continuous (values : H) :
    Continuous (fun time : ℝ =>
      closedSemigroup domain form nonnegative closable domainDense time.toNNReal values) := by
  have continuousComposition :=
    (closedSemigroup_joint_continuous domain form nonnegative closable domainDense).comp
      ((continuous_const : Continuous (fun _ : ℝ => values)).prodMk continuous_real_toNNReal)
  simpa only [Function.comp_def] using continuousComposition

theorem closedSemigroup_sub_eq_integral (time : ℝ) (timeNonnegative : 0 ≤ time)
    (values : generatorDomain domain form nonnegative closable) :
    closedSemigroup domain form nonnegative closable domainDense time.toNNReal values - values =
      -(∫ parameter in (0 : ℝ)..time,
        closedSemigroup domain form nonnegative closable domainDense parameter.toNNReal
          (closedGenerator domain form nonnegative closable domainDense values)) := by
  have integralLimit : Tendsto (fun index => ∫ parameter in (0 : ℝ)..time,
      yosidaSemigroup domain form nonnegative closable domainDense (canonicalYosidaStep index)
        (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) parameter
        (yosidaGenerator domain form nonnegative closable domainDense (canonicalYosidaStep index)
          (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) values))
      atTop (nhds (∫ parameter in (0 : ℝ)..time,
        closedSemigroup domain form nonnegative closable domainDense parameter.toNNReal
          (closedGenerator domain form nonnegative closable domainDense values))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => ‖closedGenerator domain form nonnegative closable domainDense values‖)
    · exact Eventually.of_forall fun index =>
        ((yosidaSemigroup_continuous domain form nonnegative closable domainDense _ _ _).clm_apply
          continuous_const).aestronglyMeasurable
    · refine Eventually.of_forall fun index => Filter.Eventually.of_forall fun parameter membership => ?_
      have parameterNonnegative : 0 ≤ parameter :=
        le_of_lt ((Set.uIoc_of_le timeNonnegative ▸ membership).1)
      exact yosidaSemigroup_generator_norm_bound domain form nonnegative closable domainDense
        index parameter parameterNonnegative values
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun parameter membership => ?_
      have parameterNonnegative : 0 ≤ parameter :=
        le_of_lt ((Set.uIoc_of_le timeNonnegative ▸ membership).1)
      simpa only [closedSemigroupApproximation, Real.coe_toNNReal _ parameterNonnegative] using
        closedSemigroupApproximation_generator_limit domain form nonnegative closable domainDense
          parameter.toNNReal values
  have leftLimit := (closedSemigroup_approximation_limit domain form nonnegative closable domainDense
    time.toNNReal (values : H)).sub (tendsto_const_nhds (x := (values : H)))
  have rightLimit := integralLimit.neg
  have approximationIdentity (index : ℕ) :
      closedSemigroupApproximation domain form nonnegative closable domainDense index time.toNNReal values - values =
        -(∫ parameter in (0 : ℝ)..time,
          yosidaSemigroup domain form nonnegative closable domainDense (canonicalYosidaStep index)
            (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) parameter
            (yosidaGenerator domain form nonnegative closable domainDense (canonicalYosidaStep index)
              (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) values)) := by
    simpa only [closedSemigroupApproximation, Real.coe_toNNReal _ timeNonnegative,
      yosidaSemigroup_eq_exp] using BoundedSemigroupIntegral.exp_apply_sub_eq_integral
        (yosidaGenerator domain form nonnegative closable domainDense (canonicalYosidaStep index)
          (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index)) (values : H) time
  simp_rw [← approximationIdentity] at rightLimit
  exact tendsto_nhds_unique leftLimit rightLimit

theorem closedSemigroup_hasDerivWithinAt_zero
    (values : generatorDomain domain form nonnegative closable) :
    HasDerivWithinAt (fun time : ℝ =>
      closedSemigroup domain form nonnegative closable domainDense time.toNNReal values)
      (-(closedGenerator domain form nonnegative closable domainDense values)) (Set.Ici 0) 0 := by
  have orbitContinuous := closedSemigroup_orbit_continuous domain form nonnegative closable domainDense
    (closedGenerator domain form nonnegative closable domainDense values)
  have integralDerivative := intervalIntegral.integral_hasDerivAt_right
    (orbitContinuous.intervalIntegrable (0 : ℝ) 0)
    (orbitContinuous.stronglyMeasurableAtFilter volume (nhds 0)) orbitContinuous.continuousAt
  have formulaDerivative := (integralDerivative.neg.const_add (values : H)).hasDerivWithinAt
    (s := Set.Ici (0 : ℝ))
  simp only [Real.toNNReal_zero, closedSemigroup_zero, ContinuousLinearMap.id_apply] at formulaDerivative
  apply formulaDerivative.congr_of_mem
  · intro time membership
    have identity := closedSemigroup_sub_eq_integral domain form nonnegative closable domainDense
      time membership values
    simpa only [Pi.neg_apply, add_comm] using (sub_eq_iff_eq_add.mp identity)
  · exact Set.mem_Ici.mpr le_rfl

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroupApproximation_generator_limit
#print axioms IGS.Sec31.QuadraticEnergySpace.yosidaSemigroup_generator_norm_bound
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_orbit_continuous
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_sub_eq_integral
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_hasDerivWithinAt_zero
