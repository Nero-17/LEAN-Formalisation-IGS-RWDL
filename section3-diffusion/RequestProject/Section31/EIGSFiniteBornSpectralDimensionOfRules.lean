import RequestProject.Section31.EIGSFiniteBornHeatUpperOfRules
import RequestProject.Section31.EIGSFiniteBornHeatLowerOfRules
import RequestProject.Section3.SpectralDimension

/-! Finite-born spectral dimension from the actual two-sided heat estimates.
Both estimates are supplied by the same actual compact smoothing construction.
Continuous densities of the same closed semigroup are quantified independently
of choices. No diagonal power bound or spectral dimension is a model input. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped BoundedContinuousFunction NNReal
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}

def XiFiniteBornHeatSpectralDimensionProperties (system : EIGSData K)
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
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
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
  XiFiniteBornHeatUpperProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair ∧
  XiFiniteBornHeatLowerProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair ∧
  ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair mass))),
  ∀ (birth : ℕ) (vertex : XiVtx system birth),
  ∀ kernels : ℝ≥0 → parameters.LimitSpace → parameters.LimitSpace → ℝ,
    (∀ time, 0 < time → Continuous (fun points : parameters.LimitSpace × parameters.LimitSpace =>
      kernels time points.1 points.2)) →
  ∀ lifted : ℝ≥0 → Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) →L[ℝ]
      C(parameters.LimitSpace, ℝ),
    (∀ time, 0 < time → ∀ forcing point, lifted time forcing point =
      ∫ other, kernels time point other * forcing other
        ∂xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) →
    (∀ time, 0 < time → ∀ forcing, xiContinuousL2Map system rulesConnected parameters.lengths
      parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne
      parameters.eigenpair mass (lifted time forcing) =
        QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time forcing) →
    Tendsto (fun time : ℝ => -2 * Real.log
      (kernels time.toNNReal (parameters.vertexEmbedding birth vertex) (parameters.vertexEmbedding birth vertex)) /
        Real.log time) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * ((Real.log mass.rate - Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
        Real.log (mass.rate * resistanceRate))))

theorem xiFiniteBornHeatSpectralDimensionProperties_of_compactSmoothing (system : EIGSData K)
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
    (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (compactSmoothingProperties : XiContinuousAllTimeCompactSmoothingProperties system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair) :
    XiFiniteBornHeatSpectralDimensionProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  have upperProperties := xiFiniteBornHeatUpperProperties_of_compactSmoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair primitiveDegree compactSmoothingProperties
  have lowerProperties := xiFiniteBornHeatLowerProperties_of_compactSmoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair primitiveDegree compactSmoothingProperties
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

theorem exists_xiFiniteBornHeatSpectralDimension_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive)
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
  exact xiFiniteBornHeatSpectralDimensionProperties_of_compactSmoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair primitiveDegree continuousProperties

end
end EIGS

#print axioms EIGS.xiFiniteBornHeatSpectralDimensionProperties_of_compactSmoothing
#print axioms EIGS.exists_xiFiniteBornHeatSpectralDimension_of_rules
