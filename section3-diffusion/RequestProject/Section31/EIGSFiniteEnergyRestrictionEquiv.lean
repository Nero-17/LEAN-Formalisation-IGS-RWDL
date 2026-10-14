import RequestProject.Section31.EIGSFiniteEnergyContinuousExtension
import RequestProject.Section31.EIGSFiniteEnergyContinuousExtensionOfRules
import RequestProject.Section31.EIGSL2QuadraticEnergy

/-! Restriction of the original continuous finite-energy domain to the actual
vertex union. When the resistance rate is greater than one, the constructed
extension proves surjectivity onto the entire bounded-trace-energy domain.
Injectivity uses density in the original path-metric completion. The final
consumer supplies the harmonic contraction and all eigenpair data from rules.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31
noncomputable section
variable {K : ℕ}

abbrev xiFiniteEnergyRestriction (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour) :
    xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive →ₗ[ℝ]
    xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive :=
  xiContinuousEnergyToUnionDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive

theorem xiFiniteEnergyRestriction_injective (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour) :
    Function.Injective (xiFiniteEnergyRestriction system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) := by
  intro first second equality
  apply Subtype.ext
  apply ContinuousMap.ext
  intro point
  apply (xiCompletionUnionEmbedding_denseRange system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair).induction_on point
    (isClosed_eq first.val.continuous second.val.continuous)
  intro vertex
  exact congrFun (congrArg Subtype.val equality) vertex

theorem xiFiniteEnergyRestriction_surjective_of_step_contraction
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (rateGreaterThanOne : 1 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (contractionFactor : ℝ) (factorPositive : 0 < contractionFactor) (factorStrict : contractionFactor < 1)
    (stepContraction : ∀ level (oldValues : XiVtx system level → ℝ) (edge : XiEdge system.toRuleData (level + 1)),
      |xiHarmonicStep system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
          resistanceVector vectorPositive eigenpair level oldValues (XiTail system (level + 1) edge) -
        xiHarmonicStep system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
          resistanceVector vectorPositive eigenpair level oldValues (XiHead system (level + 1) edge)| ≤
        |oldValues (XiTail system level edge.1) - oldValues (XiHead system level edge.1)| * contractionFactor) :
    Function.Surjective (xiFiniteEnergyRestriction system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate (zero_lt_one.trans rateGreaterThanOne)
      resistanceVector vectorPositive) := by
  intro values
  obtain ⟨extension, agreement, _⟩ := exists_xiFiniteEnergy_continuous_extension_of_step_contraction
    system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
    resistanceRate rateGreaterThanOne resistanceVector vectorPositive eigenpair contractionFactor
    factorPositive factorStrict stepContraction values.val values.property
  have restriction : xiContinuousUnionRestriction system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair extension = values.val := funext agreement
  have membership : extension ∈ xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate (zero_lt_one.trans rateGreaterThanOne)
      resistanceVector vectorPositive := by
    change xiContinuousUnionRestriction system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair extension ∈ _
    rw [restriction]
    exact values.property
  exact ⟨⟨extension, membership⟩, Subtype.ext restriction⟩

theorem exists_xiFiniteEnergyRestriction_bijective_of_rules
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
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    ∃ resistanceRate : ℝ, ∃ rateGreaterThanOne : 1 < resistanceRate,
    ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
    ∃ eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour,
      Function.Bijective (xiFiniteEnergyRestriction system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
        resistanceRate (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive) := by
  intro parameters distanceGreaterThanOne
  obtain ⟨resistanceRate, rateGreaterThanOne, resistanceVector, vectorPositive, eigenpair, extension⟩ :=
    exists_xiFiniteEnergy_continuous_extension_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive canonicalRateGreaterThanOne
  refine ⟨resistanceRate, rateGreaterThanOne, resistanceVector, vectorPositive, eigenpair,
    xiFiniteEnergyRestriction_injective system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
      resistanceRate (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive, ?_⟩
  intro values
  obtain ⟨continuous, agreement, _⟩ := extension values.val values.property
  have restriction : xiContinuousUnionRestriction system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair continuous =
      values.val := funext agreement
  have membership : continuous ∈ xiContinuousFiniteEnergyDomain system rulesConnected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne
      parameters.eigenpair resistanceRate (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive := by
    change xiContinuousUnionRestriction system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair continuous ∈ _
    rw [restriction]
    exact values.property
  exact ⟨⟨continuous, membership⟩, Subtype.ext restriction⟩

end
end EIGS

#print axioms EIGS.xiFiniteEnergyRestriction_injective
#print axioms EIGS.xiFiniteEnergyRestriction_surjective_of_step_contraction
#print axioms EIGS.exists_xiFiniteEnergyRestriction_bijective_of_rules
