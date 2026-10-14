import RequestProject.Section31.EIGSContinuousSemigroupSmoothingOfRules
import RequestProject.Section31.EIGSClosedSemigroupCompactness
import RequestProject.Section31.ContinuousLiftCompactFactorization

/-! The actual positive-time continuous L² lifts are compact. Half-time
factorization uses the internally proved compact actual closed semigroup. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped BoundedContinuousFunction NNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def XiContinuousSemigroupCompactSmoothingProperties (system : EIGSData K)
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
        ∀ time : ℝ≥0, 0 < time → (time : ℝ) ≤ timeThreshold →
          ∃ lifted : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) →L[ℝ]
            C(parameters.LimitSpace, ℝ),
            ‖lifted‖ ≤ Real.sqrt (upperConstant / (time : ℝ) ^
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



theorem xiContinuousSemigroupCompactSmoothingProperties_of_smoothing (system : EIGSData K)
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
    (smoothingProperties : XiContinuousSemigroupSmoothingProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair) :
    XiContinuousSemigroupCompactSmoothingProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair := by
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
  have compactProperties := xiClosedSemigroupCompactnessProperties system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  dsimp only [XiClosedSemigroupCompactnessProperties] at compactProperties
  dsimp only [XiContinuousSemigroupSmoothingProperties, XiContinuousSemigroupCompactSmoothingProperties]
    at smoothingProperties ⊢
  obtain ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd,
    semigroupContinuous, intertwining, timeThreshold, timeThresholdPositive, upperConstant,
    upperConstantPositive, smoothing⟩ := smoothingProperties
  let embedding := xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  have embeddingInjective : Function.Injective embedding := xiContinuousL2Map_injective system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair mass
  refine ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd,
    semigroupContinuous, intertwining, timeThreshold, timeThresholdPositive,
    upperConstant, upperConstantPositive, ?_⟩
  intro time timePositive timeAtMost
  obtain ⟨lifted, liftedNorm, liftedAgreement, liftedCompatibility⟩ := smoothing time timePositive timeAtMost
  let halfTime : ℝ≥0 := time / 2
  have halfTimePositive : 0 < halfTime := div_pos timePositive (by norm_num)
  have halfTimeAtMost : (halfTime : ℝ) ≤ timeThreshold := by
    have halfAtMost : halfTime ≤ time := div_le_self time.coe_nonneg (by norm_num)
    exact (show (halfTime : ℝ) ≤ (time : ℝ) from halfAtMost).trans timeAtMost
  obtain ⟨halfLifted, _, _, halfCompatibility⟩ := smoothing halfTime halfTimePositive halfTimeAtMost
  have halfAdd : halfTime + halfTime = time := by
    exact add_halves time
  have factorization :
      QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time =
      (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense halfTime).comp
        (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense halfTime) := by
    calc
      _ = QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense
          (halfTime + halfTime) := congrArg _ halfAdd.symm
      _ = _ := QuadraticEnergySpace.closedSemigroup_add originalDomain originalForm nonnegative closable originalDense
        halfTime halfTime
  have liftedCompact : IsCompactOperator lifted := continuousLift_compact_of_half_time embedding embeddingInjective
    lifted halfLifted _ _ liftedCompatibility halfCompatibility factorization
    (compactProperties originalDense halfTime halfTimePositive)
  exact ⟨lifted, liftedNorm, liftedCompact, liftedAgreement, liftedCompatibility⟩

theorem exists_xiContinuousSemigroupCompactSmoothing_of_rules (system : EIGSData K)
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
      XiContinuousSemigroupCompactSmoothingProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, continuousProperties⟩ :=
    exists_xiContinuousSemigroupSmoothing_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiContinuousSemigroupCompactSmoothingProperties_of_smoothing system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair continuousProperties

end
end EIGS

#print axioms EIGS.xiContinuousSemigroupCompactSmoothingProperties_of_smoothing
#print axioms EIGS.exists_xiContinuousSemigroupCompactSmoothing_of_rules