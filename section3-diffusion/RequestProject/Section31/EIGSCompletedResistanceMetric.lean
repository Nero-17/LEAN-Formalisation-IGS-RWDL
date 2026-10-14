import RequestProject.Section31.EIGSCompletedResistanceTriangle
import RequestProject.Section31.EIGSEnergyConstantsQuotient
import RequestProject.Section31.EIGSClosedRegularity
import RequestProject.Section31.ContinuousResistanceMetricTopology

/-! The actual completed resistance separates all original completion points.
The existing uniformly dense continuous energy core proves this internally.
Together with compact energy extension and the triangle inequality for R,
it defines the resistance metric with exactly the original topology.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (anchor : XiVertexUnion system)

local instance : CompactSpace (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :=
  xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair

variable (extension : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair anchor →L[ℝ]
  C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (agreement : ∀ values vertex, extension values (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) = values.value.val vertex)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system)

include agreement rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance mass in
theorem xiCompletedResistanceRow_injective :
    Function.Injective (xiCompletedResistanceRow system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor extension) := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  intro first second rowEquality
  have energyFunctionEquality : ∀ function : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive,
      function.val first = function.val second := by
    intro function
    let values : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive :=
      ⟨function.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, function.property⟩
    obtain ⟨normalized, normalizedProperty, _⟩ := exists_unique_xiEnergy_zero_anchored_representative system rulesConnected
      resistanceRate ratePositive resistanceVector vectorPositive anchor eigenpair values
    let anchorValue := function.val (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair anchor)
    have continuousAgreement : extension normalized.val = function.val - ContinuousMap.const _ anchorValue := by
      apply ContinuousMap.ext
      intro point
      refine (xiCompletionUnionEmbedding_denseRange system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair).induction_on point
        (isClosed_eq (extension normalized.val).continuous (function.val - ContinuousMap.const _ anchorValue).continuous) ?_
      intro vertex
      rw [agreement, normalizedProperty.1]
      rfl
    have differenceEquality := congrArg
      (fun row : xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive resistanceVector
        vectorPositive eigenpair anchor => inner ℝ row normalized) rowEquality
    dsimp only at differenceEquality
    unfold xiCompletedResistanceRow at differenceEquality
    rw [← continuousOperatorKernelRow_represents, ← continuousOperatorKernelRow_represents] at differenceEquality
    change extension normalized.val first = extension normalized.val second at differenceEquality
    rw [continuousAgreement] at differenceEquality
    change function.val first - anchorValue = function.val second - anchorValue at differenceEquality
    linarith
  by_contra distinct
  have distancePositive' : 0 < dist first second := dist_pos.mpr distinct
  let target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ) :=
    ⟨fun point => dist point first, continuous_id.dist continuous_const⟩
  obtain ⟨function, close⟩ := (xiClosedLpEnergy_regular_core system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
    metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair).1
      target (dist first second / 4) (by positivity)
  have firstClose := close first
  have secondClose := close second
  change |function.val first - dist first first| < dist first second / 4 at firstClose
  rw [dist_self, sub_zero] at firstClose
  change |function.val second - dist second first| < dist first second / 4 at secondClose
  rw [dist_comm second first] at secondClose
  have sameValue := energyFunctionEquality function
  have firstUpper := (abs_lt.mp firstClose).2
  have secondLower := (abs_lt.mp secondClose).1
  linarith

variable (extensionCompact : IsCompactOperator extension)

include agreement rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance mass extensionCompact in
def xiCompletedResistanceMetric : MetricSpace
    (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let resistance := xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
    metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension
  have rowContinuous := xiCompletedResistanceRow_continuous system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    anchor extension extensionCompact
  have rowInjective := xiCompletedResistanceRow_injective system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    anchor extension agreement rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance mass
  refine continuousResistanceMetric resistance
    (fun _ => (continuous_const.sub rowContinuous).norm.pow 2) ?_ ?_ ?_ ?_
  · intro point
    simp only [resistance, xiCompletedResistance, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · intro first second
    exact congrArg (fun value : ℝ => value ^ 2) (norm_sub_rev _ _)
  · intro first middle last
    exact xiCompletedResistance_triangle system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair
      anchor extension agreement extensionCompact first middle last
  · intro first second distinct
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    apply sub_ne_zero.mpr
    intro equality
    exact distinct (rowInjective equality)

theorem xiCompletedResistanceMetric_original_topology :
    (xiCompletedResistanceMetric system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension agreement
      rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance mass extensionCompact).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)) := rfl

theorem xiCompletedResistanceMetric_distance
    (first second : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :
    @dist _ (xiCompletedResistanceMetric system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension agreement
      rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance mass extensionCompact).toDist first second =
    xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension first second := rfl

end
end EIGS

#print axioms EIGS.xiCompletedResistanceRow_injective
#print axioms EIGS.xiCompletedResistanceMetric
#print axioms EIGS.xiCompletedResistanceMetric_original_topology
