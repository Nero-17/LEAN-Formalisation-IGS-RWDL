import RequestProject.Section31.EIGSPointEvaluation
import RequestProject.Section31.EIGSIncidenceResistanceDecayWithoutPrimitive
import RequestProject.Section31.PointwiseEnergyLimit

/-! No primitive degree-matrix assumption is needed.

Vanishing actual L² norm and bounded actual energy identify every finite
vertex value. All scale estimates are derived from the original rules. -/

namespace EIGS

open Filter Topology
open scoped BoundedContinuousFunction

variable {K : ℕ}

theorem xiContinuous_pointwise_zero_of_L2_zero_energy_bounded_without_primitive (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    ∀ (sequence : ℕ → C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
    (∀ index, xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (sequence index ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤) →
    ∀ energyBound : ℝ,
    (∀ index, (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (sequence index ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal ≤ energyBound) →
    Tendsto (fun index => ‖core.embed (BoundedContinuousFunction.mkOfCompact (sequence index))‖) atTop (nhds 0) →
    ∀ vertex : XiVertexUnion system,
    Tendsto (fun index => sequence index (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex)) atTop (nhds 0) := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  dsimp only
  intro sequence sequenceFinite energyBound energiesBounded normsTendsto vertex
  obtain ⟨birth, finiteVertex, vertexEquality⟩ := xiVertexUnion_exhausted system vertex
  obtain ⟨tailConstant, tailPositive, pointConstant, pointPositive, pointBound⟩ :=
    exists_xiContinuous_point_energy_bound system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  have errorsTendsto := (xiIncidence_resistance_inverse_tendsto_zero_without_primitive system rulesConnected
    plantingNonadjacent resistanceRate ratePositive resistanceVector vectorPositive
    eigenpair birth finiteVertex).const_mul (2 * tailConstant ^ 2 / pointConstant)
  apply IGS.Sec31.tendsto_zero_of_two_scale_energy_bounds
    (fun index => sequence index (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex))
    (fun index => ‖core.embed (BoundedContinuousFunction.mkOfCompact (sequence index))‖)
    (fun index => (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (sequence index ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal)
    (fun age => 2 * mass.rate ^ (birth + age) /
      (pointConstant * (xiVertexIncidenceCount system (birth + age) (xiForward system birth age finiteVertex) : ℝ)))
    (fun age => (2 * tailConstant ^ 2 / pointConstant) *
      (1 / ((xiVertexIncidenceCount system (birth + age) (xiForward system birth age finiteVertex) : ℝ) *
        resistanceRate ^ (birth + age)))) energyBound energiesBounded
  · intro age
    positivity
  · exact normsTendsto
  · simpa only [mul_zero] using errorsTendsto
  · intro age index
    have bound := pointBound (sequence index) (sequenceFinite index) (birth + age)
      (xiForward system birth age finiteVertex)
    simpa only [xiCompletionEmbedding, Function.comp_apply, xiVertexEmbedding_forward, vertexEquality] using bound

end EIGS

#print axioms EIGS.xiContinuous_pointwise_zero_of_L2_zero_energy_bounded_without_primitive
