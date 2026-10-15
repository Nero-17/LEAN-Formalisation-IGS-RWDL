import RequestProject.Section31.EIGSLocallyFiniteSameKernelPowerHeatExitPhysicalTight
import RequestProject.Section31.EIGSLocallyFiniteCanonicalRates

/-! The manuscript's exact Laakso/Xi kernel exponents on their literal
same-family Brownian/Hunt/exit/physical-Poisson/tight witnesses. The actual
mass and resistance computations supply the numerical exponents internally. -/
namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 12000000
variable {K : ℕ}

def locallyFiniteRuleHeatExponent (canonical : Bool) : ℝ :=
  if canonical then Real.log 6 / Real.log (33 / 2) else Real.log 6 / Real.log 18
def XiIdentifiedOriginalMeasuredGHPSPowerHeatExitPhysicalNumericalProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization) (heatExponent : ℝ) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI originalMeasuredGHPSDefinitionInstance05 := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI originalMeasuredGHPSDefinitionInstance06 : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
    ∃ semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
      XiOriginalMeasuredGHPSPowerHeatExitPhysicalTightSemigroupProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate normalization normalizationPositive
        (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
        (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
        (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense)
        heatExponent semigroup ∧
      (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
          (semigroup time function) =
        QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
          (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass function))

theorem exists_locallyFiniteRuleSystem_numerical_same_kernel_power_heat_exit_physical_tight_Brownian (canonical : Bool) :
    let system := locallyFiniteRuleSystem canonical
    let connected := locallyFiniteRuleSystem_connected canonical
    let parameters := xiPathMetricDataOfRules system connected
      (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
      (locallyFiniteRuleSystem_distancePositive canonical)
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected (locallyFiniteRuleSystem_edgesUnique canonical)
          (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical))
    let mass := xiMassParametersOfRules system connected (locallyFiniteRuleSystem_distancePositive canonical)
    letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
    ∃ resistanceVector : Fin 1 → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
    ∃ eigenpair : ∀ colour, (system.ruleFamily connected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour,
    ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily connected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      resistanceRate = locallyFiniteRuleResistance canonical ∧
      1 < resistanceRate ∧
      Nonempty (XiContinuousResistanceFormRealization system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair (xiVertexEmbedding system 0 true)) ∧
      XiResistanceFormClosedIdentification system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair ∧
      XiIdentifiedOriginalMeasuredGHPSPowerHeatExitPhysicalNumericalProperties system connected
        (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
        resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive
        (locallyFiniteRuleHeatExponent canonical) ∧
      XiIdentifiedOriginalMeasuredGHPSPowerHeatExitPhysicalTightProperties system connected
        (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
        resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiIdentifiedOriginalMeasuredGHPSPowerHeatExitPhysicalProperties system connected
        (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
        resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiIdentifiedOriginalMeasuredGHPSHuntHeatProperties system connected
        (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
        resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiIdentifiedOriginalMeasuredGHPSHuntPowerHeatProperties system connected
        (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
        resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      XiSameKernelPowerHeatEstimatesProperties system connected
        (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
        (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
        resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive ∧
      xiActualRecurrent system := by
  intro system connected parameters distanceGreaterThanOne mass
  letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) distanceGreaterThanOne parameters.eigenpair
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, rateEquality, rateGreaterThanOne,
    realization, closedIdentification, tightProperties, physicalProperties, jointProperties,
    jointPowerProperties, powerProperties, recurrence⟩ :=
      exists_locallyFiniteRuleSystem_same_kernel_power_heat_exit_physical_tight_Brownian canonical
  have massEquality : mass.rate = 6 :=
    (XiMassParameters.rate_eq_spectralRadius system mass).trans (locallyFiniteRuleSystem_massSpectralRadius canonical)
  have exponentEquality : Real.log mass.rate / Real.log (mass.rate * resistanceRate) =
      locallyFiniteRuleHeatExponent canonical := by
    rw [massEquality, rateEquality]
    cases canonical <;> norm_num [locallyFiniteRuleResistance, locallyFiniteRuleHeatExponent]
  have numericalProperties : XiIdentifiedOriginalMeasuredGHPSPowerHeatExitPhysicalNumericalProperties system connected
      (locallyFiniteRuleSystem_loopless canonical) (locallyFiniteRuleSystem_edgesUnique canonical)
      (locallyFiniteRuleSystem_plantingNonadjacent canonical) (locallyFiniteRuleSystem_distancePositive canonical)
      resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive
      (locallyFiniteRuleHeatExponent canonical) := by
    dsimp only [XiIdentifiedOriginalMeasuredGHPSPowerHeatExitPhysicalTightProperties] at tightProperties
    obtain ⟨originalDense, semigroup, semigroupProperties, intertwining⟩ := tightProperties
    dsimp only [XiIdentifiedOriginalMeasuredGHPSPowerHeatExitPhysicalNumericalProperties]
    refine ⟨originalDense, semigroup, ?_, intertwining⟩
    simpa only [exponentEquality] using semigroupProperties
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, eigenpair,
    normalization, normalizationPositive, normalizedConvergence, rateEquality, rateGreaterThanOne,
    realization, closedIdentification, numericalProperties, tightProperties, physicalProperties,
    jointProperties, jointPowerProperties, powerProperties, recurrence⟩

end
end EIGS

#print axioms EIGS.exists_locallyFiniteRuleSystem_numerical_same_kernel_power_heat_exit_physical_tight_Brownian
