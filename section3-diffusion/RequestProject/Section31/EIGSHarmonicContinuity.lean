import RequestProject.Section31.EIGSHarmonicLipschitzApproximation
import RequestProject.Section31.EIGSMetricOfRules
import Mathlib.Topology.ContinuousMap.Basic

set_option maxHeartbeats 1600000

/-! The actual harmonic union extension is uniformly continuous for the
constructed path metric and therefore extends continuously to its completion.
The final theorem constructs all resistance and metric data from the original
rule assumptions; neither continuity nor a cell diameter estimate is assumed. -/

namespace EIGS

open Filter Topology

variable {K : ℕ}

theorem xiHarmonicUnionExtension_uniformContinuous_of_edge_decay
    (system : EIGSData K) (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (contractionFactor initialBound : ℝ) (factorPositive : 0 < contractionFactor)
    (factorStrict : contractionFactor < 1) (boundNonnegative : 0 ≤ initialBound)
    (edgeDecay : ∀ offset (edge : XiEdge system.toRuleData (initialLevel + offset)),
      |xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues offset (XiTail system (initialLevel + offset) edge) -
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues offset (XiHead system (initialLevel + offset) edge)| ≤
        contractionFactor ^ offset * initialBound) :
    letI := xiUnionMetricSpace system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair
    UniformContinuous (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel initialValues) := by
  letI := xiUnionMetricSpace system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair
  obtain ⟨minimumLength, minimumLengthPositive, lengthLowerBound⟩ :=
    exists_positive_colour_length_lower_bound system lengths lengthsPositive
  have errorConvergence : Tendsto (fun offset : ℕ => contractionFactor ^ offset *
      (initialBound / (1 - contractionFactor) + initialBound / minimumLength *
        (xiRuleRadius system lengths / (1 - distanceRate⁻¹)) * distanceRate⁻¹)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one factorPositive.le factorStrict).mul_const
        (initialBound / (1 - contractionFactor) + initialBound / minimumLength *
          (xiRuleRadius system lengths / (1 - distanceRate⁻¹)) * distanceRate⁻¹)
  apply Metric.uniformContinuous_iff.2
  intro tolerance tolerancePositive
  obtain ⟨coarseOffset, errorSmall⟩ :=
    (errorConvergence.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < tolerance / 3))).exists
  obtain ⟨approximation, approximationLipschitz, approximationError⟩ := exists_xiHarmonic_lipschitz_approximation
    system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
    resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
    initialLevel initialValues contractionFactor initialBound factorPositive factorStrict boundNonnegative edgeDecay
    minimumLength minimumLengthPositive lengthLowerBound coarseOffset
  obtain ⟨distanceTolerance, distanceTolerancePositive, approximationContinuous⟩ :=
    Metric.uniformContinuous_iff.1 approximationLipschitz.uniformContinuous (tolerance / 3) (by positivity)
  refine ⟨distanceTolerance, distanceTolerancePositive, ?_⟩
  intro source sink pointsClose
  have firstError := (approximationError source).trans_lt errorSmall
  have secondError := (approximationError sink).trans_lt errorSmall
  have middleError := approximationContinuous pointsClose
  rw [Real.dist_eq] at middleError
  have triangle := abs_sub_le
    (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      renormalizationEigenpair initialLevel initialValues source) (approximation source)
    (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      renormalizationEigenpair initialLevel initialValues sink)
  have secondTriangle := abs_sub_le (approximation source) (approximation sink)
    (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
      renormalizationEigenpair initialLevel initialValues sink)
  rw [abs_sub_comm (approximation sink)] at secondTriangle
  rw [Real.dist_eq]
  linarith

theorem exists_xiHarmonic_completion_extension_of_edge_decay
    (system : EIGSData K) (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (contractionFactor initialBound : ℝ) (factorPositive : 0 < contractionFactor)
    (factorStrict : contractionFactor < 1) (boundNonnegative : 0 ≤ initialBound)
    (edgeDecay : ∀ offset (edge : XiEdge system.toRuleData (initialLevel + offset)),
      |xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues offset (XiTail system (initialLevel + offset) edge) -
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues offset (XiHead system (initialLevel + offset) edge)| ≤
        contractionFactor ^ offset * initialBound) :
    ∃ extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
      ∀ vertex : XiVertexUnion system,
        extension (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
        xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
          renormalizationEigenpair initialLevel initialValues vertex := by
  letI := xiUnionMetricSpace system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair
  have harmonicContinuous := xiHarmonicUnionExtension_uniformContinuous_of_edge_decay
    system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
    resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
    initialLevel initialValues contractionFactor initialBound factorPositive factorStrict boundNonnegative edgeDecay
  refine ⟨⟨UniformSpace.Completion.extension (xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel initialValues),
    UniformSpace.Completion.continuous_extension⟩, ?_⟩
  intro vertex
  exact UniformSpace.Completion.extension_coe harmonicContinuous vertex

theorem exists_xiContinuousHarmonics_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ resistanceRatePositive : 0 < resistanceRate,
      ∃ resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∀ initialLevel (initialValues : XiVtx system initialLevel → ℝ),
        ∃ extension : C(parameters.LimitSpace, ℝ),
          ∀ offset (vertex : XiVtx system (initialLevel + offset)),
            extension (parameters.vertexEmbedding (initialLevel + offset) vertex) =
              xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
                renormalizationEigenpair initialLevel initialValues offset vertex := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro oneColour colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, resistanceRatePositive, resistanceVectorPositive, renormalizationEigenpair,
      contractionFactor, factorPositive, factorStrict, stepContraction⟩ :=
    exists_xiHarmonic_strict_contraction system rulesConnected distancePositive oneColourDistance
  refine ⟨resistanceRate, resistanceVector, resistanceRatePositive, resistanceVectorPositive, renormalizationEigenpair, ?_⟩
  intro initialLevel initialValues
  have initialEdgeBound : ∀ edge : XiEdge system.toRuleData initialLevel,
      |initialValues (XiTail system initialLevel edge) - initialValues (XiHead system initialLevel edge)| ≤ 2 * ‖initialValues‖ := by
    intro edge
    have firstBound := norm_le_pi_norm initialValues (XiTail system initialLevel edge)
    have secondBound := norm_le_pi_norm initialValues (XiHead system initialLevel edge)
    rw [Real.norm_eq_abs] at firstBound secondBound
    exact (abs_sub _ _).trans (by linarith)
  have edgeDecay := xiHarmonicValues_edge_decay_of_step_contraction system rulesConnected resistanceRate resistanceRatePositive
    resistanceVector resistanceVectorPositive renormalizationEigenpair contractionFactor factorPositive.le stepContraction
    initialLevel initialValues (2 * ‖initialValues‖) initialEdgeBound
  obtain ⟨extension, extensionValues⟩ := exists_xiHarmonic_completion_extension_of_edge_decay
    system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceRateGreaterThanOne parameters.eigenpair resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
    renormalizationEigenpair initialLevel initialValues contractionFactor (2 * ‖initialValues‖) factorPositive factorStrict
    (by positivity) edgeDecay
  refine ⟨extension, ?_⟩
  intro offset vertex
  exact (extensionValues (xiVertexEmbedding system (initialLevel + offset) vertex)).trans
    (xiHarmonicUnionExtension_values system rulesConnected resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex)

end EIGS
