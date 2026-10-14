import RequestProject.Section31.EIGSContinuousAllTimeCompactSmoothingOfRules

/-! Any continuous L2 lift intertwining the same actual closed semigroup
is compact at positive times. Compact smoothing is constructed internally
from the original rules and the already available continuous semigroup
properties; actual embedding injectivity identifies the constructed lift
with the supplied kernel lift. Compactness is not an assumption.
Candidate source: no compilation is claimed. -/

namespace EIGS
open MeasureTheory Filter Topology IGS.Sec31
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}

def XiSameClosedSemigroupLiftCompactProperties (system : EIGSData K)
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
      ∀ time : ℝ≥0, 0 < time →
      ∀ lifted : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass) →L[ℝ]
        C(parameters.LimitSpace, ℝ),
      (∀ forcing,
        xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass (lifted forcing) =
        QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time forcing) →
      IsCompactOperator lifted

theorem xiSameClosedSemigroupLiftCompactProperties_of_rules (system : EIGSData K)
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
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) : XiSameClosedSemigroupLiftCompactProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
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
  dsimp only [XiSameClosedSemigroupLiftCompactProperties]
  intro originalDense semigroup semigroupNorm semigroupZero semigroupAdd semigroupContinuous intertwining
  have continuousProperties : XiContinuousSemigroupProperties
    system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
    dsimp only [XiContinuousSemigroupProperties]
    exact ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, intertwining⟩
  have smoothing := xiContinuousSemigroupSmoothingProperties_of_continuousSemigroup system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair continuousProperties
  have compactSmoothing := xiContinuousSemigroupCompactSmoothingProperties_of_smoothing system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair smoothing
  have allTimeCompact := xiContinuousAllTimeCompactSmoothingProperties_of_compactSmoothing system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair compactSmoothing
  dsimp only [XiContinuousAllTimeCompactSmoothingProperties] at allTimeCompact
  obtain ⟨compactDense, compactSemigroup, _, _, _, _, _,
    timeThreshold, timeThresholdPositive, upperConstant, upperConstantPositive, allLifts⟩ := allTimeCompact
  have denseEquality : compactDense = originalDense := Subsingleton.elim _ _
  subst compactDense
  intro time timePositive lifted liftedCompatibility
  obtain ⟨constructedLift, _, constructedCompact, _, constructedCompatibility⟩ := allLifts time timePositive
  have liftEquality : constructedLift = lifted := by
    apply ContinuousLinearMap.ext
    intro forcing
    apply xiContinuousL2Map_injective system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    exact (constructedCompatibility forcing).trans (liftedCompatibility forcing).symm
  rw [← liftEquality]
  exact constructedCompact

end
end EIGS

#print axioms EIGS.xiSameClosedSemigroupLiftCompactProperties_of_rules
