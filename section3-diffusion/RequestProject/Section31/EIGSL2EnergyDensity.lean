import RequestProject.Section31.EIGSL2QuadraticEnergy
import RequestProject.Section31.EIGSHarmonicL2Density

/-! The actual continuous finite-energy subspace is dense in the constructed
limit L². Resistance and metric parameters are chosen from the original
rules; no density, support or weak convergence hypothesis is supplied. -/

namespace EIGS

open MeasureTheory Filter Topology Metric
open scoped ENNReal

variable {K : ℕ}

theorem exists_xiDenseLpQuadraticEnergy_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system connected distancePositive
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ resistanceRatePositive : 0 < resistanceRate,
      ∃ resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily connected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      Dense (xiContinuousEnergyLpDomain system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive :
          Set (Lp ℝ 2 (xiLimitMeasure system connected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass))) ∧
      (∀ function, 0 ≤ xiContinuousLpEnergyQuadraticForm system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair function) := by
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  have rateGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system connected distancePositive
  letI := xiCompletion_compactSpace system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system connected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass
  obtain ⟨resistanceRate, resistanceVector, resistanceRatePositive, resistanceVectorPositive,
      renormalizationEigenpair, harmonicDense⟩ :=
    exists_xiContinuousHarmonic_L2_dense_core_of_rules system connected loopless unique plantingNonadjacent distancePositive
  refine ⟨resistanceRate, resistanceVector, resistanceRatePositive, resistanceVectorPositive, renormalizationEigenpair,
    ?_, ?_⟩
  · apply Metric.dense_iff.mpr
    intro target tolerance tolerancePositive
    obtain ⟨initialLevel, initialValues, extension, extensionValues, extensionEnergy, _, approximation⟩ :=
      harmonicDense target tolerance tolerancePositive
    have classEquality :
        xiContinuousL2Map system connected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass extension =
        core.embed (BoundedContinuousFunction.mkOfCompact extension) := rfl
    refine ⟨xiContinuousL2Map system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass extension, ?_, ?_⟩
    · change dist _ target < tolerance
      rw [classEquality, dist_eq_norm]
      exact approximation
    · apply (xiContinuousEnergyLpDomain_mem system connected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass
        resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive extension).mpr
      exact ne_of_eq_of_ne extensionEnergy ENNReal.ofReal_ne_top
  · exact xiContinuousLpEnergyQuadraticForm_nonnegative system connected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius connected) rateGreaterThanOne parameters.eigenpair mass
      resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair

end EIGS

#print axioms EIGS.exists_xiDenseLpQuadraticEnergy_of_rules
