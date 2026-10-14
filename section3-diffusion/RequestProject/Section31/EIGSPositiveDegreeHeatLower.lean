import RequestProject.Section31.EIGSFiniteBornHeatLowerOfRules
import RequestProject.Section31.EIGSPositiveDegreeRieszDiagonalLower

/-! Positive degree eigenpair version on the original state space, measure,
closed form and semigroup. Existing universal heat-property definitions are
retained verbatim. Candidate source; no compilation is claimed. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped BigOperators Classical BoundedContinuousFunction ENNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiFiniteBornHeatLowerProperties_of_compactSmoothing_of_positive_degree_data (system : EIGSData K)
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
    XiFiniteBornHeatLowerProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI finiteBornHeatLowerProofCompact := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI finiteBornHeatLowerProofLimitCompact : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
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
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  dsimp only [XiFiniteBornHeatLowerProperties]
  refine ⟨xiContinuousAllTimeHeatKernelDensityProperties_of_compactSmoothing system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair compactSmoothingProperties, ?_⟩
  dsimp only [XiContinuousAllTimeCompactSmoothingProperties] at compactSmoothingProperties
  obtain ⟨smoothingDense, _, _, _, _, _, _, _, _, _, _, smoothing⟩ := compactSmoothingProperties
  intro originalDense birth vertex
  have densityEquality : smoothingDense = originalDense := Subsingleton.elim _ _
  subst smoothingDense
  obtain ⟨lowerConstant, cutoffTime, lowerPositive, cutoffTimePositive, cutoffTimeAtMostOne, rieszBound⟩ := exists_xiFiniteBorn_riesz_diagonal_lower_of_positive_degree_data
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair degreeData originalDense birth vertex
  refine ⟨lowerConstant, cutoffTime, lowerPositive, cutoffTimePositive, cutoffTimeAtMostOne, ?_⟩
  intro time timePositive timeAtMostCutoff kernel kernelContinuous lifted representation compatibility
  obtain ⟨halfLift, _, halfCompact, _, halfCompatibility⟩ := smoothing (time / 2) (by positivity)
  have diagonalEquality := continuousKernel_diagonal_eq_half_time_row
    (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
    originalDomain originalForm nonnegative closable originalDense
    (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
    (xiContinuousL2Map_injective system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
    (fun function => ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) _ function)
    time halfLift lifted halfCompact halfCompatibility compatibility kernel kernelContinuous representation
    (parameters.vertexEmbedding birth vertex)
  rw [diagonalEquality]
  exact rieszBound time timePositive timeAtMostCutoff halfLift halfCompatibility

theorem exists_xiFiniteBornHeatLower_of_rules_of_positive_degree_data (system : EIGSData K)
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
      XiFiniteBornHeatLowerProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, continuousProperties⟩ :=
    exists_xiContinuousAllTimeCompactSmoothing_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiFiniteBornHeatLowerProperties_of_compactSmoothing_of_positive_degree_data system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair degreeData continuousProperties



end
end EIGS

#print axioms EIGS.xiFiniteBornHeatLowerProperties_of_compactSmoothing_of_positive_degree_data
#print axioms EIGS.exists_xiFiniteBornHeatLower_of_rules_of_positive_degree_data

