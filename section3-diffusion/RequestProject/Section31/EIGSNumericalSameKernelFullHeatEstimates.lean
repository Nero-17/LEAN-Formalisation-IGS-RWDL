import RequestProject.Section31.EIGSSameNativeJointFullHeatEstimatesOfRules

/-! Numerical exponents for every kernel of one original closed form.
The actual rule consumer supplies these exponents internally. -/
namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal BoundedContinuousFunction
noncomputable section
variable {K : ℕ}

def XiNumericalSameKernelFullHeatEstimatesProperties (system : EIGSData K)
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
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (finiteExponent typicalExponent baseLogExponent : ℝ) : Prop :=
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
  ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
  ∀ semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
    (∀ time, ‖semigroup time‖ ≤ 1) →
    semigroup 0 = ContinuousLinearMap.id ℝ C(parameters.LimitSpace, ℝ) →
    (∀ firstTime secondTime, semigroup (firstTime + secondTime) =
      (semigroup firstTime).comp (semigroup secondTime)) →
    Continuous (fun point : C(parameters.LimitSpace, ℝ) × ℝ≥0 => semigroup point.2 point.1) →
    (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
      xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
        (semigroup time function) =
      QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
        (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass function)) →
    ∀ timeThreshold upperConstant : ℝ, 0 < timeThreshold → 0 < upperConstant →
    ∀ kernel : {time : ℝ≥0 // 0 < time} → parameters.LimitSpace → parameters.LimitSpace → ℝ,
      PositiveClosedKernelData
        (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
        (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
        (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense)
        (Real.log mass.rate / Real.log (mass.rate * resistanceRate)) semigroup timeThreshold upperConstant kernel →
      PositiveKernelFullHeatEstimates
        (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass)
        parameters.vertexEmbedding
        finiteExponent typicalExponent baseLogExponent kernel

theorem xiNumericalSameKernelFullHeatEstimatesProperties_of_canonical
    (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily connected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (finiteExponent typicalExponent baseLogExponent : ℝ)
    (finiteEquality :
      (Real.log (xiMassParametersOfRules system connected distancePositive).rate -
        Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system))) /
        Real.log ((xiMassParametersOfRules system connected distancePositive).rate * resistanceRate) = finiteExponent)
    (typicalEquality : Real.log (xiMassParametersOfRules system connected distancePositive).rate /
      Real.log ((xiMassParametersOfRules system connected distancePositive).rate * resistanceRate) = typicalExponent)
    (logEquality : 1 / (Real.log (xiMassParametersOfRules system connected distancePositive).rate /
      Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) - 1) = baseLogExponent)
    (estimates : XiSameKernelFullHeatEstimatesProperties system connected loopless unique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair normalization normalizationPositive) :
    XiNumericalSameKernelFullHeatEstimatesProperties system connected loopless unique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair normalization normalizationPositive finiteExponent typicalExponent baseLogExponent := by
  rw [← finiteEquality, ← typicalEquality, ← logEquality]
  exact estimates

end
end EIGS

#print axioms EIGS.xiNumericalSameKernelFullHeatEstimatesProperties_of_canonical
