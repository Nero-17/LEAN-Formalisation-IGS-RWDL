import RequestProject.Section31.EIGSUnitUniformConvergence
import RequestProject.Section31.EIGSHarmonicL2Recovery
import RequestProject.Section31.VaryingL2Approximation

/-! Native speed-measure L² recovery for the actual original-unit fine-graph
Dirichlet minimizers. The sequence uses each original graph level. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

set_option maxHeartbeats 1800000

variable {K : ℕ}

theorem xiFiniteSpeedL2_sub_norm_le (system : EIGSData K) (mass : XiMassParameters system)
    (level : ℕ) (first second : XiVtx system level → ℝ) :
    ‖xiFiniteSpeedL2 system mass level first - xiFiniteSpeedL2 system mass level second‖ ≤ ‖first - second‖ := by
  have massOne : measureUnivNNReal (xiVertexSpeedMeasure system mass level) = 1 := by
    simp [measureUnivNNReal]
  have representativeBound : ∀ᵐ vertex ∂xiVertexSpeedMeasure system mass level,
      ‖(xiFiniteSpeedL2 system mass level first - xiFiniteSpeedL2 system mass level second) vertex‖ ≤ ‖first - second‖ := by
    filter_upwards [Lp.coeFn_sub (xiFiniteSpeedL2 system mass level first) (xiFiniteSpeedL2 system mass level second),
      xiFiniteSpeedL2_ae system mass level first, xiFiniteSpeedL2_ae system mass level second]
      with vertex subtraction firstValue secondValue
    rw [subtraction, Pi.sub_apply, firstValue, secondValue]
    exact norm_le_pi_norm (first - second) vertex
  simpa only [massOne, NNReal.coe_one, Real.one_rpow, one_mul] using
    Lp.norm_le_of_ae_bound (norm_nonneg (first - second)) representativeBound

noncomputable def xiUnitNativeL2 (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (initialLevel : ℕ)
    (initialValues : XiVtx system initialLevel → ℝ) (level : ℕ) :
    Lp ℝ 2 (xiVertexSpeedMeasure system mass level) :=
  if afterInitial : initialLevel ≤ level then
    xiFiniteSpeedL2 system mass level
      (xiUnitPotentialAt system rulesConnected initialLevel level afterInitial initialValues)
  else 0

theorem xiUnitNativeL2_at_level (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (initialLevel level : ℕ) (afterInitial : initialLevel ≤ level)
    (initialValues : XiVtx system initialLevel → ℝ) :
    xiUnitNativeL2 system rulesConnected mass initialLevel initialValues level =
      xiFiniteSpeedL2 system mass level
        (xiUnitPotentialAt system rulesConnected initialLevel level afterInitial initialValues) := by
  rw [xiUnitNativeL2, dif_pos afterInitial]

theorem xiUnitNativeL2_strong_of_uniform (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system) (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (uniformConvergence : Tendsto (xiUnitPotentialUniformError system rulesConnected initialLevel initialValues
      (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)) atTop (nhds 0)) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    (xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass).Strong
      (xiUnitNativeL2 system rulesConnected mass initialLevel initialValues)
      ((xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass).embed (BoundedContinuousFunction.mkOfCompact extension)) := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  apply core.strong_of_norm_sub_tendsto_zero _
    (fun level => core.restrict level (BoundedContinuousFunction.mkOfCompact extension)) _
    (core.strong_restrict (BoundedContinuousFunction.mkOfCompact extension))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ uniformConvergence
  filter_upwards [eventually_ge_atTop initialLevel] with level afterInitial
  rw [xiUnitNativeL2_at_level system rulesConnected mass initialLevel level afterInitial,
    show core.restrict level (BoundedContinuousFunction.mkOfCompact extension) = _ from
      xiSpeedL2Core_restrict_eq_finiteSpeedL2 system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass (BoundedContinuousFunction.mkOfCompact extension) level,
    xiUnitPotentialUniformError, dif_pos afterInitial]
  exact xiFiniteSpeedL2_sub_norm_le system mass level _ _

end EIGS
