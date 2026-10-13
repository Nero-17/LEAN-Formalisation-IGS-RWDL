import RequestProject.Section31.EIGSContinuousSemigroupOfRules
import RequestProject.Section31.EIGSConservativeMarkovSemigroup
import RequestProject.Section31.ContinuousMarkovPointMeasure

/-! The same continuous semigroup identified with the actual closed L²
semigroup is positive and preserves every constant at every point. Full support
removes the exceptional sets. Riesz representation then gives continuous
probability-valued point maps. The final consumer has only the five original
rule hypotheses; path convergence is a separate theorem. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical NNReal
noncomputable section
set_option maxHeartbeats 4000000

variable {K : ℕ}

def XiContinuousSemigroupMarkovProperties (system : EIGSData K)
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
  letI : MeasurableSpace parameters.LimitSpace := borel parameters.LimitSpace
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
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
      (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
        (∀ point, 0 ≤ function point) → ∀ point, 0 ≤ semigroup time function point) ∧
      (∀ (time : ℝ≥0) (constant : ℝ),
        semigroup time (ContinuousMap.const _ constant) = ContinuousMap.const _ constant) ∧
      ∃ transition : ℝ≥0 → parameters.LimitSpace → ProbabilityMeasure parameters.LimitSpace,
        (∀ time, Continuous (transition time)) ∧
        ∀ (time : ℝ≥0) (point : parameters.LimitSpace) (function : C(parameters.LimitSpace, ℝ)),
          ∫ location, function location ∂(transition time point) = semigroup time function point

theorem xiContinuousSemigroupMarkovProperties_of_continuousSemigroup (system : EIGSData K)
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
    (continuousProperties : XiContinuousSemigroupProperties system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair) :
    XiContinuousSemigroupMarkovProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
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
  letI : MeasurableSpace parameters.LimitSpace := borel parameters.LimitSpace
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
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
  dsimp only [XiContinuousSemigroupProperties, XiContinuousSemigroupMarkovProperties]
    at continuousProperties ⊢
  obtain ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd,
    semigroupContinuous, intertwining⟩ := continuousProperties
  have closedProperties := xiConservativeMarkovSemigroupProperties_of_dense_core system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair originalDense
  dsimp only [XiConservativeMarkovSemigroupProperties] at closedProperties
  obtain ⟨closedDense, closedMarkov, closedConstants, _, _, _, _⟩ := closedProperties
  have densityEquality : closedDense = originalDense := Subsingleton.elim _ _
  subst closedDense
  let measure := xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  let embedding := xiContinuousL2Map system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  have embeddingAE (function : C(parameters.LimitSpace, ℝ)) :
      (embedding function : parameters.LimitSpace → ℝ) =ᵐ[measure] function := by
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) measure function
  have positive (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ))
      (nonnegativeFunction : ∀ point, 0 ≤ function point) :
      ∀ point, 0 ≤ semigroup time function point := by
    have inputNonnegative : ∀ᵐ point ∂measure, 0 ≤ embedding function point := by
      filter_upwards [embeddingAE function] with point representative
      rw [representative]
      exact nonnegativeFunction point
    have outputNonnegative := (closedMarkov time (embedding function)).1 inputNonnegative
    rw [← intertwining time function] at outputNonnegative
    have continuousNonnegative : ∀ᵐ point ∂measure, 0 ≤ semigroup time function point := by
      filter_upwards [outputNonnegative, embeddingAE (semigroup time function)]
        with point nonnegativeValue representative
      change 0 ≤ embedding (semigroup time function) point at nonnegativeValue
      rw [representative] at nonnegativeValue
      exact nonnegativeValue
    have denseNonnegative : Dense {point : parameters.LimitSpace | 0 ≤ semigroup time function point} :=
      measure.dense_of_ae continuousNonnegative
    have closedNonnegative : IsClosed {point : parameters.LimitSpace | 0 ≤ semigroup time function point} :=
      isClosed_le continuous_const (semigroup time function).continuous
    intro point
    simpa only [closedNonnegative.closure_eq, Set.mem_setOf_eq] using denseNonnegative point
  have embeddingConstant (constant : ℝ) :
      embedding (ContinuousMap.const parameters.LimitSpace constant) =
        (xiContinuousLpEnergyConstant system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
          resistanceRate ratePositive resistanceVector vectorPositive constant : Lp ℝ 2 measure) := by
    apply Lp.ext
    exact (embeddingAE (ContinuousMap.const parameters.LimitSpace constant)).trans
      (xiContinuousLpEnergyConstant_ae system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive constant).symm
  have preservesConstants (time : ℝ≥0) (constant : ℝ) :
      semigroup time (ContinuousMap.const parameters.LimitSpace constant) =
        ContinuousMap.const parameters.LimitSpace constant := by
    apply xiContinuousL2Map_injective system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    rw [intertwining, embeddingConstant, closedConstants constant time, ← embeddingConstant]
  have preservesOne (time : ℝ≥0) : semigroup time 1 = 1 := by
    simpa using preservesConstants time 1
  refine ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd,
    semigroupContinuous, intertwining, positive, preservesConstants, ?_⟩
  refine ⟨fun time => ContinuousMarkov.pointProbabilityMeasure (semigroup time)
    (positive time) (preservesOne time), ?_, ?_⟩
  · intro time
    exact ContinuousMarkov.pointProbabilityMeasure_continuous (semigroup time)
      (positive time) (preservesOne time)
  · intro time point function
    exact ContinuousMarkov.pointProbabilityMeasure_integral (semigroup time)
      (positive time) (preservesOne time) point function

theorem exists_xiContinuousSemigroupMarkov_of_rules (system : EIGSData K)
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
      XiContinuousSemigroupMarkovProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, continuousProperties⟩ :=
    exists_xiContinuousSemigroup_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiContinuousSemigroupMarkovProperties_of_continuousSemigroup system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair continuousProperties

end
end EIGS

#print axioms EIGS.xiContinuousSemigroupMarkovProperties_of_continuousSemigroup
#print axioms EIGS.exists_xiContinuousSemigroupMarkov_of_rules
