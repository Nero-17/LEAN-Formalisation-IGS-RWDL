import RequestProject.Section31.ProbabilityL2PoincareClosure
import RequestProject.Section31.QuadraticEnergySemigroupSmoothing
import RequestProject.Section31.QuadraticEnergySemigroupIntegralPreservation
import Mathlib.Analysis.SpecificLimits.Basic

/-! Poincaré and the proved energy smoothing estimate imply convergence to
the invariant mean. This does not assert positivity improvement or analytic
time dependence of the semigroup. The actual-rule consumer supplies the
Poincaré inequality and the zero-energy constant internally. -/

namespace IGS.Sec31.QuadraticEnergySpace

open MeasureTheory Filter Topology
open scoped NNReal
noncomputable section

variable {Space : Type*} [MeasurableSpace Space]
    (law : Measure Space) [IsProbabilityMeasure law]
    (domain : Submodule ℝ (Lp ℝ 2 law)) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values)
    (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set (Lp ℝ 2 law)))

theorem closedSemigroup_mean_zero_projection_bound (constant : ℝ)
    (constantNonnegative : 0 ≤ constant)
    (varianceBound : ∀ target : closedDomain domain form nonnegative,
      (∫ point, (target.val point - ∫ other, target.val other ∂law) ^ 2 ∂law) ≤
        constant * closedForm domain form nonnegative closable target)
    (time : ℝ≥0) (timePositive : 0 < time) (forcing : Lp ℝ 2 law) :
    ‖probabilityL2MeanZeroProjection law
        (closedSemigroup domain form nonnegative closable domainDense time forcing)‖ ^ 2 ≤
      constant * (‖forcing‖ ^ 2 / (2 * (time : ℝ))) := by
  obtain ⟨lifted, liftedEquality, energyBound⟩ := closedSemigroup_exists_energy_bound
    domain form nonnegative closable domainDense time timePositive forcing
  rw [← liftedEquality, probabilityL2MeanZeroProjection_norm_sq]
  exact (varianceBound lifted).trans (mul_le_mul_of_nonneg_left energyBound constantNonnegative)

theorem closedSemigroup_mean_zero_projection_tendsto (constant : ℝ)
    (constantNonnegative : 0 ≤ constant)
    (varianceBound : ∀ target : closedDomain domain form nonnegative,
      (∫ point, (target.val point - ∫ other, target.val other ∂law) ^ 2 ∂law) ≤
        constant * closedForm domain form nonnegative closable target)
    (forcing : Lp ℝ 2 law) :
    Tendsto (fun index : ℕ => probabilityL2MeanZeroProjection law
      (closedSemigroup domain form nonnegative closable domainDense (index + 1) forcing))
      atTop (𝓝 0) := by
  have upperLimit : Tendsto (fun index : ℕ =>
      constant * (‖forcing‖ ^ 2 / (2 * ((index : ℝ) + 1)))) atTop (𝓝 0) := by
    have shifted := (tendsto_const_div_atTop_nhds_zero_nat
      (constant * ‖forcing‖ ^ 2 / 2 : ℝ)).comp (tendsto_add_atTop_nat 1)
    convert shifted using 1
    ext index
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring
  have squareLimit : Tendsto (fun index : ℕ => ‖probabilityL2MeanZeroProjection law
      (closedSemigroup domain form nonnegative closable domainDense (index + 1) forcing)‖ ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _ upperLimit
    intro index
    simpa only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using
      closedSemigroup_mean_zero_projection_bound law domain form nonnegative closable domainDense
        constant constantNonnegative varianceBound (index + 1) (by positivity) forcing
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using squareLimit.sqrt

theorem closedSemigroup_tendsto_mean (constant : ℝ)
    (constantNonnegative : 0 ≤ constant)
    (varianceBound : ∀ target : closedDomain domain form nonnegative,
      (∫ point, (target.val point - ∫ other, target.val other ∂law) ^ 2 ∂law) ≤
        constant * closedForm domain form nonnegative closable target)
    (one : domain) (oneEnergy : form one = 0)
    (oneAE : ∀ᵐ point ∂law, (one : Lp ℝ 2 law) point = 1)
    (forcing : Lp ℝ 2 law) :
    Tendsto (fun index : ℕ =>
      closedSemigroup domain form nonnegative closable domainDense (index + 1) forcing)
      atTop (𝓝 ((∫ point, forcing point ∂law) • Lp.const 2 law (1 : ℝ))) := by
  have projectionIdentity : ∀ time : ℝ≥0,
      probabilityL2MeanZeroProjection law
          (closedSemigroup domain form nonnegative closable domainDense time forcing) =
        closedSemigroup domain form nonnegative closable domainDense time forcing -
          (∫ point, forcing point ∂law) • Lp.const 2 law (1 : ℝ) := by
    intro time
    simp only [probabilityL2MeanZeroProjection, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [L2_inner_one_eq_integral,
      closedSemigroup_integral_preservation law domain form nonnegative closable domainDense
        one oneEnergy oneAE]
  have convergence := (closedSemigroup_mean_zero_projection_tendsto law domain form nonnegative
    closable domainDense constant constantNonnegative varianceBound forcing).add_const
      ((∫ point, forcing point ∂law) • Lp.const 2 law (1 : ℝ))
  simpa only [projectionIdentity, sub_add_cancel, zero_add] using convergence

end
end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_mean_zero_projection_bound
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_mean_zero_projection_tendsto
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_tendsto_mean
