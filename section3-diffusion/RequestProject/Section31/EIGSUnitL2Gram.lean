import RequestProject.Section31.EIGSUnitL2Recovery

/-! Actual native speed-L² scalar products of original-unit harmonic rows. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

variable {K : ℕ}

theorem xiUnitNativeL2_inner_tendsto_of_uniform (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system) (firstLevel secondLevel : ℕ)
    (firstValues : XiVtx system firstLevel → ℝ) (secondValues : XiVtx system secondLevel → ℝ)
    (firstExtension secondExtension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (firstUniform : Tendsto (xiUnitPotentialUniformError system rulesConnected firstLevel firstValues
      (firstExtension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)) atTop (nhds 0))
    (secondUniform : Tendsto (xiUnitPotentialUniformError system rulesConnected secondLevel secondValues
      (secondExtension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)) atTop (nhds 0)) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    Tendsto (fun level => inner ℝ
      (xiUnitNativeL2 system rulesConnected mass firstLevel firstValues level)
      (xiUnitNativeL2 system rulesConnected mass secondLevel secondValues level)) atTop
      (nhds (inner ℝ (core.embed (BoundedContinuousFunction.mkOfCompact firstExtension))
        (core.embed (BoundedContinuousFunction.mkOfCompact secondExtension)))) := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  exact (xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass).strong_inner_tendsto
      (xiUnitNativeL2_strong_of_uniform system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass firstLevel firstValues firstExtension firstUniform)
      (xiUnitNativeL2_strong_of_uniform system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass secondLevel secondValues secondExtension secondUniform)

end EIGS
