import RequestProject.Section31.EIGSFiniteBornSpectralDimensionOfRules
import RequestProject.Section31.EIGSPositiveDegreeHeatUpper
import RequestProject.Section31.EIGSPositiveDegreeHeatLower

/-! Positive degree eigenpair version on the original state space, measure,
closed form and semigroup. Existing universal heat-property definitions are
retained verbatim. Candidate source; no compilation is claimed. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical BoundedContinuousFunction ENNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiFiniteBornHeatSpectralDimensionProperties_of_compactSmoothing_of_positive_degree_data (system : EIGSData K)
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
    (degreeData : XiPositiveDegreeSpectralData system)
    (compactSmoothingProperties : XiContinuousAllTimeCompactSmoothingProperties system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair) :
    XiFiniteBornHeatSpectralDimensionProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  have upperProperties := xiFiniteBornHeatUpperProperties_of_compactSmoothing_of_positive_degree_data system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair degreeData compactSmoothingProperties
  have lowerProperties := xiFiniteBornHeatLowerProperties_of_compactSmoothing_of_positive_degree_data system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair degreeData compactSmoothingProperties
  dsimp only [XiFiniteBornHeatSpectralDimensionProperties]
  refine ⟨upperProperties, lowerProperties, ?_⟩
  dsimp only [XiFiniteBornHeatUpperProperties] at upperProperties
  dsimp only [XiFiniteBornHeatLowerProperties] at lowerProperties
  intro originalDense birth vertex kernels kernelsContinuous lifted representation compatibility
  obtain ⟨upperConstant, upperPositive, upperBound⟩ := upperProperties.2 originalDense birth vertex
  obtain ⟨lowerConstant, cutoffTime, lowerPositive, cutoffPositive, cutoffAtMostOne, lowerBound⟩ :=
    lowerProperties.2 originalDense birth vertex
  apply IGS.tendsto_spectral_dimension_of_pure_bounds _ _ lowerConstant upperConstant cutoffTime
    lowerPositive upperPositive cutoffPositive
  · intro time timeInRange
    have timePositive : 0 < time.toNNReal := Real.toNNReal_pos.mpr timeInRange.1
    have timeBound : (time.toNNReal : ℝ) ≤ cutoffTime := by
      simpa only [Real.coe_toNNReal time timeInRange.1.le] using timeInRange.2.le
    have bound := lowerBound time.toNNReal timePositive timeBound (kernels time.toNNReal)
      (kernelsContinuous _ timePositive) (lifted time.toNNReal)
      (representation _ timePositive) (compatibility _ timePositive)
    simpa only [Real.coe_toNNReal time timeInRange.1.le,
      Real.rpow_neg timeInRange.1.le, div_eq_mul_inv] using bound
  · intro time timeInRange
    have timePositive : 0 < time.toNNReal := Real.toNNReal_pos.mpr timeInRange.1
    have timeBound : (time.toNNReal : ℝ) ≤ 1 := by
      rw [Real.coe_toNNReal time timeInRange.1.le]
      exact timeInRange.2.le.trans cutoffAtMostOne
    have bound := upperBound time.toNNReal timePositive timeBound (kernels time.toNNReal)
      (kernelsContinuous _ timePositive) (lifted time.toNNReal)
      (representation _ timePositive) (compatibility _ timePositive)
    simpa only [Real.coe_toNNReal time timeInRange.1.le,
      Real.rpow_neg timeInRange.1.le, div_eq_mul_inv] using bound

theorem exists_xiFiniteBornHeatSpectralDimension_of_rules_of_positive_degree_data (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (degreeData : XiPositiveDegreeSpectralData system)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      XiFiniteBornHeatSpectralDimensionProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, continuousProperties⟩ :=
    exists_xiContinuousAllTimeCompactSmoothing_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiFiniteBornHeatSpectralDimensionProperties_of_compactSmoothing_of_positive_degree_data system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair degreeData continuousProperties


end
end EIGS

#print axioms EIGS.xiFiniteBornHeatSpectralDimensionProperties_of_compactSmoothing_of_positive_degree_data
#print axioms EIGS.exists_xiFiniteBornHeatSpectralDimension_of_rules_of_positive_degree_data

