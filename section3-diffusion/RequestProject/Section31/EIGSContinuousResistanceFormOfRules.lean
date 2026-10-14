import RequestProject.Section31.EIGSContinuousResistanceFormAxioms

/-! A full resistance-form realization on the same original completion.
For a given positive resistance eigenpair with rate greater than one, all
extension, compactness, resistance axioms and original-topology metric data
are constructed from the actual substitution rules. This can therefore be
applied to the exact eigenpair selected by the existing Hunt construction.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31
noncomputable section
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

structure XiContinuousResistanceFormRealization where
  extension : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
    eigenpair anchor →L[ℝ] C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)
  extension_agrees : ∀ values vertex, extension values
    (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) = values.value.val vertex
  extension_compact : IsCompactOperator extension
  resistance_form_axioms : ContinuousResistanceFormAxioms
    (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
    (xiZeroAnchoredEnergyDomain system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor)
    (xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive)
    (xiContinuousResistanceQuadraticForm system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair)
    (xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension)
  resistance_metric : MetricSpace (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
  original_topology : resistance_metric.toTopologicalSpace = inferInstance
  resistance_distance : ∀ first second, @dist _ resistance_metric.toDist first second =
    xiCompletedResistance system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor extension first second

theorem exists_xiContinuousResistanceFormRealization_of_rules
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
    (rateGreaterThanOne : 1 < resistanceRate) :
    Nonempty (XiContinuousResistanceFormRealization system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor) := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
      profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system rulesConnected
    distancePositive oneColourDistance resistanceVector vectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair profiles profilesPlus profilesMinus profilesMinimal contractionFactor profilesOscillation
  have bijective : Function.Bijective (xiFiniteEnergyRestriction system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) :=
    ⟨xiFiniteEnergyRestriction_injective system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive,
      xiFiniteEnergyRestriction_surjective_of_step_contraction system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair resistanceRate rateGreaterThanOne resistanceVector vectorPositive eigenpair
        contractionFactor factorPositive factorStrict stepContraction⟩
  obtain ⟨extension, agreement⟩ := exists_xiAnchoredEnergy_continuous_linear_extension_of_bijective system rulesConnected
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector
    vectorPositive eigenpair anchor bijective
  have compact := xiAnchoredEnergy_continuous_extension_isCompact system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate rateGreaterThanOne resistanceVector vectorPositive eigenpair
    contractionFactor factorPositive factorStrict stepContraction anchor extension agreement
  refine ⟨{
    extension := extension
    extension_agrees := agreement
    extension_compact := compact
    resistance_form_axioms := xiContinuousResistanceForm_axioms system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor
      extension agreement rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance mass
    resistance_metric := xiCompletedResistanceMetric system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive eigenpair anchor
      extension agreement rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance mass compact
    original_topology := rfl
    resistance_distance := fun _ _ => rfl }⟩

end
end EIGS

#print axioms EIGS.exists_xiContinuousResistanceFormRealization_of_rules
