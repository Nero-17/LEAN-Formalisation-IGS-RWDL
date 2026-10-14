import RequestProject.Section31.EIGSContinuousSemigroupCompactSmoothingOfRules

/-! Compact continuous L² lifts at every positive time. A small positive time
is clipped at the proved smoothing threshold; the remaining actual semigroup
factor is a contraction. No large-time smoothing premise is assumed. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped BoundedContinuousFunction NNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def XiContinuousAllTimeCompactSmoothingProperties (system : EIGSData K)
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
  ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
    ∃ semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
      (∀ time, ‖semigroup time‖ ≤ 1) ∧
      semigroup 0 = ContinuousLinearMap.id ℝ C(parameters.LimitSpace, ℝ) ∧
      (∀ firstTime secondTime, semigroup (firstTime + secondTime) =
        (semigroup firstTime).comp (semigroup secondTime)) ∧
      Continuous (fun point : C(parameters.LimitSpace, ℝ) × ℝ≥0 => semigroup point.2 point.1) ∧
      (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
          (semigroup time function) =
        QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
          (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass function)) ∧
      ∃ timeThreshold : ℝ, 0 < timeThreshold ∧ ∃ upperConstant : ℝ, 0 < upperConstant ∧
        ∀ time : ℝ≥0, 0 < time →
          ∃ lifted : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) →L[ℝ]
            C(parameters.LimitSpace, ℝ),
            ‖lifted‖ ≤ Real.sqrt (upperConstant / (min (time : ℝ) timeThreshold) ^
              (Real.log mass.rate / Real.log (mass.rate * resistanceRate))) ∧
            IsCompactOperator lifted ∧
            (∀ function : C(parameters.LimitSpace, ℝ),
              lifted (xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
                (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass function) =
                semigroup time function) ∧
            ∀ forcing : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
                (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass),
              xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
                (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
                (lifted forcing) =
              QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time forcing




theorem xiContinuousAllTimeCompactSmoothingProperties_of_compactSmoothing (system : EIGSData K)
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
    (compactSmoothingProperties : XiContinuousSemigroupCompactSmoothingProperties system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair) :
    XiContinuousAllTimeCompactSmoothingProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
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
  dsimp only [XiContinuousSemigroupCompactSmoothingProperties, XiContinuousAllTimeCompactSmoothingProperties]
    at compactSmoothingProperties ⊢
  obtain ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd,
    semigroupContinuous, intertwining, timeThreshold, timeThresholdPositive, upperConstant,
    upperConstantPositive, smoothing⟩ := compactSmoothingProperties
  let embedding := xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  have embeddingInjective : Function.Injective embedding := xiContinuousL2Map_injective system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair mass
  refine ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd,
    semigroupContinuous, intertwining, timeThreshold, timeThresholdPositive,
    upperConstant, upperConstantPositive, ?_⟩
  intro time timePositive
  let clippedTime : ℝ≥0 := min time ⟨timeThreshold, timeThresholdPositive.le⟩
  have clippedPositive : 0 < clippedTime := lt_min timePositive timeThresholdPositive
  have clippedAtMost : (clippedTime : ℝ) ≤ timeThreshold := min_le_right _ _
  have clippedAtMostTime : clippedTime ≤ time := min_le_left _ _
  obtain ⟨smallLifted, smallNorm, smallCompact, _, smallCompatibility⟩ :=
    smoothing clippedTime clippedPositive clippedAtMost
  let remainingOperator := QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable
    originalDense (time - clippedTime)
  let lifted := smallLifted.comp remainingOperator
  have liftedCompatibility (forcing) : embedding (lifted forcing) =
      QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time forcing := by
    change embedding (smallLifted (remainingOperator forcing)) = _
    rw [smallCompatibility]
    change ((QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense clippedTime).comp
      remainingOperator) forcing = _
    rw [← QuadraticEnergySpace.closedSemigroup_add, add_tsub_cancel_of_le clippedAtMostTime]
  have liftedAgreement (function : C(parameters.LimitSpace, ℝ)) :
      lifted (embedding function) = semigroup time function := by
    apply embeddingInjective
    rw [liftedCompatibility, intertwining]
  have liftedCompact : IsCompactOperator lifted := smallCompact.comp_clm remainingOperator
  have liftedNorm : ‖lifted‖ ≤ Real.sqrt (upperConstant / (min (time : ℝ) timeThreshold) ^
      (Real.log mass.rate / Real.log (mass.rate * resistanceRate))) := by
    have remainingNorm : ‖remainingOperator‖ ≤ 1 := QuadraticEnergySpace.closedSemigroup_norm
      originalDomain originalForm nonnegative closable originalDense (time - clippedTime)
    calc
      ‖lifted‖ ≤ ‖smallLifted‖ * ‖remainingOperator‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖smallLifted‖ * 1 := mul_le_mul_of_nonneg_left remainingNorm (norm_nonneg smallLifted)
      _ = ‖smallLifted‖ := mul_one _
      _ ≤ _ := by simpa only [clippedTime, NNReal.coe_min, NNReal.coe_mk] using smallNorm
  exact ⟨lifted, liftedNorm, liftedCompact, liftedAgreement, liftedCompatibility⟩

theorem exists_xiContinuousAllTimeCompactSmoothing_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
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
      XiContinuousAllTimeCompactSmoothingProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, continuousProperties⟩ :=
    exists_xiContinuousSemigroupCompactSmoothing_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiContinuousAllTimeCompactSmoothingProperties_of_compactSmoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair continuousProperties

end
end EIGS

#print axioms EIGS.xiContinuousAllTimeCompactSmoothingProperties_of_compactSmoothing
#print axioms EIGS.exists_xiContinuousAllTimeCompactSmoothing_of_rules