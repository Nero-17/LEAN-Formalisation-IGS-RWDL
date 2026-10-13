import RequestProject.Section31.EIGSUnitL2Recovery
import RequestProject.Section31.EIGSUnitEnergyRecovery
import RequestProject.Section31.EIGSHarmonicL2Density

/-! Original-rule construction of actual original-unit harmonic state and
energy recovery. No trace, harmonic convergence or recovery premise is used. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal

set_option maxHeartbeats 1800000

variable {K : ℕ}

theorem exists_xiUnitPotential_state_energy_recovery_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    ∃ resistanceRate normalization : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ normalizationPositive : 0 < normalization,
      ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∀ initialLevel (initialValues : XiVtx system initialLevel → ℝ),
        ∃ extension : C(parameters.LimitSpace, ℝ),
          (∀ vertex : XiVertexUnion system,
            extension (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair vertex) =
              xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
                renormalizationEigenpair initialLevel initialValues vertex) ∧
          xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (extension ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair) =
            ENNReal.ofReal ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive initialLevel).energy
              initialValues) ∧
          Tendsto (xiUnitPotentialUniformError system rulesConnected initialLevel initialValues
            (extension ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair)) atTop (nhds 0) ∧
          core.Strong (xiUnitNativeL2 system rulesConnected mass initialLevel initialValues)
            (core.embed (BoundedContinuousFunction.mkOfCompact extension)) ∧
          Tendsto (xiUnitPotentialScaledEnergy system rulesConnected resistanceRate normalization initialLevel initialValues)
            atTop (nhds ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive initialLevel).energy
              initialValues)) := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceRate, normalization, resistanceVector, ratePositive, normalizationPositive,
      vectorPositive, normalized, eigenpair, normalizedConvergence⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_normalized_iterate_limit coloursPositive distancePositive
  have coordinateEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour :=
    fun colour => congrFun eigenpair colour
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro oneColour colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
      profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system rulesConnected
    distancePositive oneColourDistance resistanceVector vectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive coordinateEigenpair profiles profilesPlus profilesMinus profilesMinimal
    contractionFactor profilesOscillation
  refine ⟨resistanceRate, normalization, resistanceVector, ratePositive, normalizationPositive, vectorPositive, coordinateEigenpair, ?_⟩
  intro initialLevel initialValues
  have initialEdgeBound : ∀ edge : XiEdge system.toRuleData initialLevel,
      |initialValues (XiTail system initialLevel edge) - initialValues (XiHead system initialLevel edge)| ≤ 2 * ‖initialValues‖ := by
    intro edge
    have firstBound := norm_le_pi_norm initialValues (XiTail system initialLevel edge)
    have secondBound := norm_le_pi_norm initialValues (XiHead system initialLevel edge)
    rw [Real.norm_eq_abs] at firstBound secondBound
    exact (abs_sub _ _).trans (by linarith)
  have edgeDecay := xiHarmonicValues_edge_decay_of_step_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive coordinateEigenpair contractionFactor factorPositive.le stepContraction initialLevel
    initialValues (2 * ‖initialValues‖) initialEdgeBound
  obtain ⟨extension, extensionAgreement⟩ := exists_xiHarmonic_completion_extension_of_edge_decay system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne
    parameters.eigenpair resistanceRate ratePositive resistanceVector vectorPositive coordinateEigenpair initialLevel initialValues
    contractionFactor (2 * ‖initialValues‖) factorPositive factorStrict (by positivity) edgeDecay
  have uniformConvergence : Tendsto (xiUnitPotentialUniformError system rulesConnected initialLevel initialValues
      (extension ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair)) atTop (nhds 0) := by
    have unionAgreement : extension ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair =
        xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          coordinateEigenpair initialLevel initialValues := funext extensionAgreement
    rw [unionAgreement]
    exact xiUnitPotentialUniformError_tendsto_of_edge_decay system rulesConnected resistanceRate normalization ratePositive
      normalizationPositive resistanceVector vectorPositive coordinateEigenpair normalizedConvergence initialLevel initialValues
      (xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        coordinateEigenpair initialLevel initialValues)
      (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        coordinateEigenpair initialLevel initialValues) contractionFactor (2 * ‖initialValues‖) factorPositive.le factorStrict
      (by positivity) edgeDecay
  have extensionValues : ∀ offset (vertex : XiVtx system (initialLevel + offset)),
      extension (parameters.vertexEmbedding (initialLevel + offset) vertex) =
        xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          coordinateEigenpair initialLevel initialValues offset vertex := by
    intro offset vertex
    exact (extensionAgreement (xiVertexEmbedding system (initialLevel + offset) vertex)).trans
      (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        coordinateEigenpair initialLevel initialValues offset vertex)
  refine ⟨extension, extensionAgreement, ?_, uniformConvergence, ?_, ?_⟩
  · exact xiContinuousHarmonic_extended_energy system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair resistanceRate ratePositive
      resistanceVector vectorPositive coordinateEigenpair initialLevel initialValues extension extensionValues
  · exact xiUnitNativeL2_strong_of_uniform system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass initialLevel initialValues
      extension uniformConvergence
  · exact xiUnitPotentialScaledEnergy_tendsto system rulesConnected resistanceRate normalization ratePositive normalizationPositive
      resistanceVector vectorPositive normalizedConvergence initialLevel initialValues

end EIGS
