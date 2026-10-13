import RequestProject.Section31.EIGSHarmonicJointUniform
import RequestProject.Section31.EIGSHarmonicJointEnergy

/-! Actual harmonic cores approximate every continuous finite-energy target
jointly in actual limit L² and residual energy. No joint-density premise is used. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

set_option maxHeartbeats 1800000

variable {K : ℕ}

theorem exists_xiContinuousHarmonic_joint_recovery (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (targetFinite : xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    ∃ approximation : ℕ → C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
      (∀ level (vertex : XiVertexUnion system),
        approximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
          xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
            renormalizationEigenpair level (fun finiteVertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level finiteVertex)) vertex) ∧
      Tendsto (fun level => ‖BoundedContinuousFunction.mkOfCompact (approximation level) - BoundedContinuousFunction.mkOfCompact target‖)
        atTop (nhds 0) ∧
      Tendsto (fun level => ‖core.embed (BoundedContinuousFunction.mkOfCompact (approximation level)) -
        core.embed (BoundedContinuousFunction.mkOfCompact target)‖) atTop (nhds 0) ∧
      Tendsto (fun level => (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (approximation level ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal) atTop
        (nhds ((xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
          (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal)) ∧
      Tendsto (fun level => (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (fun vertex => target (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) -
          approximation level (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex))).toReal) atTop (nhds 0) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
      profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system rulesConnected
    distancePositive oneColourDistance resistanceVector vectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair profiles profilesPlus profilesMinus profilesMinimal contractionFactor profilesOscillation
  choose approximation approximationAgreement using fun level =>
    exists_xiContinuousHarmonic_of_step_contraction system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair contractionFactor factorPositive factorStrict
      stepContraction level (fun vertex => target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex))
  have uniformConvergence := xiContinuousHarmonicProjection_uniform_tendsto system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
    metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair contractionFactor factorPositive factorStrict
    stepContraction target (CompactSpace.uniformContinuous_of_continuous target.continuous) approximation approximationAgreement
  refine ⟨approximation, approximationAgreement, uniformConvergence, ?_, ?_, ?_⟩
  · apply squeeze_zero (fun _ => norm_nonneg _) _ uniformConvergence
    intro level
    rw [← map_sub]
    exact IGS.Sec31.boundedContinuous_L2_norm_le_sup
      (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass)
      (BoundedContinuousFunction.mkOfCompact (approximation level) - BoundedContinuousFunction.mkOfCompact target)
  · exact xiContinuousHarmonicProjection_energy_tendsto system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair target approximation approximationAgreement targetFinite
  · exact xiContinuousHarmonicProjection_residual_energy_tendsto system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair target approximation approximationAgreement targetFinite

end EIGS
