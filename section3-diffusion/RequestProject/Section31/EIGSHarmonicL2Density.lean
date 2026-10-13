import RequestProject.Section31.EIGSHarmonicL2Recovery
import RequestProject.Section31.VaryingL2Approximation

/-! A dense core of actual continuous, finite-energy harmonic functions in
the constructed speed-measure L² space. The actual weighted harmonic native
classes recover each core function strongly at every original graph level.
This does not assert convergence of original unit-resistance fine profiles. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal

set_option maxHeartbeats 1800000

variable {K : ℕ}

theorem xiContinuousHarmonic_extended_energy (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRatePositive : 0 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      distanceRatePositive metricEigenpair, ℝ))
    (extensionValues : ∀ offset (vertex : XiVtx system (initialLevel + offset)),
      extension (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        distanceRatePositive metricEigenpair (initialLevel + offset) vertex) =
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex) :
    xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        distanceRatePositive metricEigenpair) =
      ENNReal.ofReal ((xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive initialLevel).energy initialValues) := by
  have unionAgreement :
      extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        distanceRatePositive metricEigenpair =
      xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues := by
    funext vertex
    obtain ⟨level, membership⟩ := xiVertexUnion_exhausted system vertex
    have fineMembership := xiLevelVertices_monotone system
      (by omega : level ≤ initialLevel + level) membership
    obtain ⟨finiteVertex, representation⟩ := fineMembership
    rw [← representation]
    exact (extensionValues level finiteVertex).trans
      (xiHarmonicUnionExtension_values system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues level finiteVertex).symm
  rw [unionAgreement]
  exact xiHarmonicUnionExtension_energy system rulesConnected resistanceRate resistanceRatePositive resistanceVector
    resistanceVectorPositive renormalizationEigenpair initialLevel initialValues

theorem exists_xiContinuousHarmonic_L2_dense_core_of_rules (system : EIGSData K)
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
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ resistanceRatePositive : 0 < resistanceRate,
      ∃ resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∀ (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass))
        (tolerance : ℝ), 0 < tolerance →
        ∃ initialLevel : ℕ, ∃ initialValues : XiVtx system initialLevel → ℝ,
          ∃ extension : C(parameters.LimitSpace, ℝ),
            (∀ offset (vertex : XiVtx system (initialLevel + offset)),
              extension (parameters.vertexEmbedding (initialLevel + offset) vertex) =
              xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
                resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex) ∧
            xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
              (extension ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
                (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair) =
              ENNReal.ofReal ((xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
                resistanceVectorPositive initialLevel).energy initialValues) ∧
            core.Strong (xiHarmonicNativeL2 system rulesConnected mass resistanceRate resistanceRatePositive
              resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel initialValues)
              (core.embed (BoundedContinuousFunction.mkOfCompact extension)) ∧
            ‖core.embed (BoundedContinuousFunction.mkOfCompact extension) - target‖ < tolerance := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace :=
    parameters.limit_compactSpace rulesUnique plantingNonadjacent distancePositive
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
  obtain ⟨resistanceRate, resistanceVector, resistanceRatePositive, resistanceVectorPositive,
      renormalizationEigenpair, harmonicDense⟩ :=
    exists_xiContinuousHarmonic_dense_core_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, resistanceVector, resistanceRatePositive, resistanceVectorPositive, renormalizationEigenpair, ?_⟩
  intro target tolerance tolerancePositive
  obtain ⟨continuousTarget, targetClose⟩ := core.dense.exists_dist_lt target (half_pos tolerancePositive)
  obtain ⟨initialLevel, initialValues, extension, extensionValues, uniformClose⟩ :=
    harmonicDense continuousTarget.toContinuousMap (tolerance / 2) (half_pos tolerancePositive)
  let harmonicFunction : XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact extension
  have boundedDistance : ‖harmonicFunction - continuousTarget‖ < tolerance / 2 := by
    apply (BoundedContinuousFunction.norm_lt_iff_of_compact (half_pos tolerancePositive)).2
    intro point
    simpa only [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs] using uniformClose point
  have embeddedDistance :
      ‖core.embed harmonicFunction - core.embed continuousTarget‖ < tolerance / 2 := by
    rw [← map_sub]
    exact (IGS.Sec31.boundedContinuous_L2_norm_le_sup
      (xiLimitProbabilityMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass)
      (harmonicFunction - continuousTarget)).trans_lt boundedDistance
  refine ⟨initialLevel, initialValues, extension, extensionValues, ?_, ?_, ?_⟩
  · exact xiContinuousHarmonic_extended_energy system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair resistanceRate
      resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel initialValues
      extension extensionValues
  · exact xiHarmonicNativeL2_strong system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass resistanceRate
      resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel initialValues
      extension extensionValues
  · have targetDistance : ‖core.embed continuousTarget - target‖ < tolerance / 2 := by
      simpa only [dist_eq_norm, norm_sub_rev] using targetClose
    calc
      _ ≤ ‖core.embed harmonicFunction - core.embed continuousTarget‖ +
          ‖core.embed continuousTarget - target‖ := by
            simpa only [dist_eq_norm] using dist_triangle (core.embed harmonicFunction) (core.embed continuousTarget) target
      _ < tolerance := by linarith

end EIGS
