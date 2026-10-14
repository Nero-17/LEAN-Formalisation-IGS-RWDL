import RequestProject.Section31.EIGSAddressCellAverageEnergy

/-! The level-zero address partition is the whole space. Its energy error
therefore gives a genuine global variance estimate on the continuous energy
core. This is a precursor to the closed-form Poincare inequality; no claim
of irreducibility or strictly positive heat kernels is made here. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical BigOperators
noncomputable section
variable {K : ℕ}

theorem xiAddressCellAverage_zero (system : EIGSData K) (mass : XiMassParameters system)
    (values : XiEdgeAddress system → ℝ) (address : XiEdgeAddress system) :
    xiAddressCellAverage system mass 0 values address = ∫ sample, values sample ∂mass.addressMeasure := by
  letI : Subsingleton (XiEdge system.toRuleData 0) := by
    change Subsingleton Unit
    infer_instance
  have cellUniv (edge : XiEdge system.toRuleData 0) :
      {sample | xiAddressEdge system 0 sample = edge} = Set.univ := by
    ext sample
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have weightOne (edge : XiEdge system.toRuleData 0) : mass.edgeWeight 0 edge = 1 := by
    change mass.amplitude system.initCol / (mass.rate ^ 0 * mass.amplitude system.initCol) = 1
    simp only [pow_zero, one_mul]
    exact div_self (mass.amplitude_positive system.initCol).ne'
  simp only [xiAddressCellAverage, xiAddressCellMean, cellUniv, weightOne, setIntegral_univ, div_one]

theorem exists_xiAddressPoincare_bound_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      4 ≤ mass.rate * resistanceRate ∧ ∃ constant : ℝ, 0 < constant ∧
      ∀ (target : C(XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair, ℝ)),
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (target ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair) ≠ ⊤ →
      (∫ address, (target (xiAddressLimit system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair address) -
        ∫ sample, target (xiAddressLimit system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair sample)
            ∂mass.addressMeasure) ^ 2 ∂mass.addressMeasure) ≤
        constant * (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
          (target ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair)).toReal := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      scaleBound, constant, constantPositive, errorBound⟩ :=
    exists_xiAddressCellAverage_energy_error_bound_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    scaleBound, constant, constantPositive, ?_⟩
  intro target finiteEnergy
  simpa only [pow_zero, div_one, xiAddressCellAverage_zero] using errorBound target finiteEnergy 0

end
end EIGS

#print axioms EIGS.xiAddressCellAverage_zero
#print axioms EIGS.exists_xiAddressPoincare_bound_of_rules
