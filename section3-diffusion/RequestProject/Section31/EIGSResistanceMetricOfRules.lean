import RequestProject.Section31.EIGSCompletedResistanceMetric
import RequestProject.Section31.EIGSSkeletonResistanceFiniteIdentification

/-! Original rules in the canonical resistance-rate-greater-than-one regime
construct a resistance metric on the same original completion. The metric has
exactly the original topology and equals the scaled actual effective resistance
on every finite skeleton. Compact extension and the resistance triangle are
proved internally in the prerequisite chain, not final model assumptions.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem exists_xiResistanceMetric_of_rules
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (canonicalRateGreaterThanOne : 1 < system.resistanceSpectralRadius rulesConnected distancePositive) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∃ resistanceRate : ℝ, ∃ rateGreaterThanOne : 1 < resistanceRate,
    ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
    ∃ eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour,
    ∃ metric : MetricSpace parameters.LimitSpace,
      metric.toTopologicalSpace = inferInstance ∧
      ∀ level (source sink : XiVtx system level) (distinct : source ≠ sink),
        @dist _ metric.toDist (parameters.vertexEmbedding level source) (parameters.vertexEmbedding level sink) =
        (XiNetwork system level).effRes source sink
          ((XiNetwork system level).flow_nonempty_of_connected
            (xiSimpleGraph_connected system rulesConnected level) source sink distinct) resistanceVector /
          resistanceRate ^ level := by
  intro parameters
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, rateGreaterThanOne, resistanceVector, vectorPositive, eigenpair, extensions⟩ :=
    exists_xiAnchoredEnergy_compact_continuous_extension_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive canonicalRateGreaterThanOne
  let anchor := xiVertexEmbedding system 0 true
  obtain ⟨extension, extensionCompact, agreement⟩ := extensions anchor
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  let metric := xiCompletedResistanceMetric system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair resistanceRate
    (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive eigenpair anchor extension agreement
    rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance mass extensionCompact
  refine ⟨resistanceRate, rateGreaterThanOne, resistanceVector, vectorPositive, eigenpair, metric, rfl, ?_⟩
  intro level source sink distinct
  change xiCompletedResistance system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair resistanceRate
    (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive eigenpair anchor extension
    (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceGreaterThanOne)
      parameters.eigenpair (xiVertexEmbedding system level source))
    (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceGreaterThanOne)
      parameters.eigenpair (xiVertexEmbedding system level sink)) = _
  rw [xiCompletedResistance_on_skeleton system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair resistanceRate
    (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive eigenpair anchor extension agreement]
  exact xiSkeletonResistance_eq_finite_effRes system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
    resistanceVector vectorPositive eigenpair anchor level source sink distinct

end
end EIGS

#print axioms EIGS.exists_xiResistanceMetric_of_rules
