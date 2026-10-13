import RequestProject.Section31.EIGSL2Closability
import RequestProject.Section31.EIGSL2EnergyDensity
import RequestProject.Section31.QuadraticEnergyCompletion

/-! A dense, nonnegative closed quadratic energy in the actual limit L²,
constructed from the rules. Its energy-plus-L² domain is complete, and it
extends the actual continuous trace energy exactly. The Markov property of
the closure and varying-space Mosco statements remain separate results. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31

set_option maxHeartbeats 2400000

variable {K : ℕ}

theorem exists_xiClosedLpQuadraticEnergy_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ closedDomain : Submodule ℝ (Lp ℝ 2 (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass)),
      ∃ closedForm : QuadraticForm ℝ closedDomain, ∃ closedNonnegative : ∀ values, 0 ≤ closedForm values,
      CompleteSpace (QuadraticEnergySpace closedDomain closedForm closedNonnegative) ∧
      Dense (closedDomain : Set (Lp ℝ 2 (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass))) ∧
      (∀ values : xiContinuousEnergyLpDomain system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass
          resistanceRate ratePositive resistanceVector vectorPositive,
        ∃ membership : values.val ∈ closedDomain,
          closedForm ⟨values.val, membership⟩ =
          xiContinuousLpEnergyQuadraticForm system connected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass
            resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair values) ∧
      (∀ values : QuadraticEnergySpace closedDomain closedForm closedNonnegative,
        ‖values‖ ^ 2 = closedForm values.value + ‖values.value.val‖ ^ 2) := by
  classical
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  have rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system connected distancePositive
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive,
      renormalizationEigenpair, originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system connected loopless unique plantingNonadjacent distancePositive
  let originalDomain := xiContinuousEnergyLpDomain system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (connected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable system connected loopless unique plantingNonadjacent distancePositive
      oneColourDistance primitiveDegree parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy (by simpa using ambientZero.norm)
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
    QuadraticEnergySpace.closedDomain originalDomain originalForm originalNonnegative,
    QuadraticEnergySpace.closedForm originalDomain originalForm originalNonnegative closable,
    QuadraticEnergySpace.closedForm_nonnegative originalDomain originalForm originalNonnegative closable,
    QuadraticEnergySpace.closedEnergySpace_complete originalDomain originalForm originalNonnegative closable,
    QuadraticEnergySpace.closedDomain_dense originalDomain originalForm originalNonnegative originalDense, ?_, ?_⟩
  · intro values
    exact ⟨QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm originalNonnegative values,
      QuadraticEnergySpace.closedForm_extends originalDomain originalForm originalNonnegative closable values⟩
  · exact QuadraticEnergySpace.norm_sq _ _ _

end EIGS

#print axioms EIGS.exists_xiClosedLpQuadraticEnergy_of_rules
