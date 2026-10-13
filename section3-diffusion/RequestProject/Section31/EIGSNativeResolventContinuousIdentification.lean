import RequestProject.Section31.EIGSNativeResolventUniformSubsequence
import RequestProject.Section31.EIGSNativeResolventConvergence
import RequestProject.Section31.EIGSL2EnergyRepresentative

/-! Continuous representatives of the actual closed resolvent, obtained from
actual finite resolvents. Uniform finite-vertex limits are transported to the
varying speed-measure L² core. The closed resolvent is then identified by its
already proved Strong limit. The step range remains 0 < step ≤ 1. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiNativeL2_strong_of_uniform_subsequence
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected)
    (mass : XiMassParameters system)
    (selection : ℕ → ℕ) (selectionStrict : StrictMono selection)
    (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (limit : C(parameters.LimitSpace, ℝ))
    (uniformConvergence : Tendsto (fun index =>
      ‖fun vertex : XiVtx system (selection index) => sequence (selection index) vertex -
        limit (parameters.vertexEmbedding (selection index) vertex)‖) atTop (nhds 0)) :
    letI := xiCompletion_compactSpace system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair
    letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    (core.reindex selection selectionStrict.tendsto_atTop).Strong
      (fun index => sequence (selection index)) (core.embed (BoundedContinuousFunction.mkOfCompact limit)) := by
  letI := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  have referenceStrong : (core.reindex selection selectionStrict.tendsto_atTop).Strong
      (fun index => core.restrict (selection index) (BoundedContinuousFunction.mkOfCompact limit))
      (core.embed (BoundedContinuousFunction.mkOfCompact limit)) :=
    core.strong_reindex selection selectionStrict.tendsto_atTop
      (sequence := fun level => core.restrict level (BoundedContinuousFunction.mkOfCompact limit))
      (limit := core.embed (BoundedContinuousFunction.mkOfCompact limit))
      (core.strong_restrict (BoundedContinuousFunction.mkOfCompact limit))
  have differenceConverges : Tendsto (fun index =>
      ‖sequence (selection index) - core.restrict (selection index) (BoundedContinuousFunction.mkOfCompact limit)‖)
      atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun index =>
      norm_nonneg (sequence (selection index) -
        core.restrict (selection index) (BoundedContinuousFunction.mkOfCompact limit))) _ uniformConvergence
    apply Eventually.of_forall
    intro index
    have restrictionEquality : core.restrict (selection index) (BoundedContinuousFunction.mkOfCompact limit) =
        xiFiniteSpeedL2 system mass (selection index)
          (fun vertex => limit (parameters.vertexEmbedding (selection index) vertex)) :=
      xiSpeedL2Core_restrict_eq_finiteSpeedL2 system rulesConnected parameters.lengths
        parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        distanceGreaterThanOne parameters.eigenpair mass (BoundedContinuousFunction.mkOfCompact limit)
        (selection index)
    have estimate := xiFiniteSpeedL2_sub_norm_le system mass (selection index)
      (fun vertex => sequence (selection index) vertex)
      (fun vertex => limit (parameters.vertexEmbedding (selection index) vertex))
    simpa only [xiFiniteSpeedL2_representative, ← restrictionEquality] using estimate
  exact (core.reindex selection selectionStrict.tendsto_atTop).strong_of_norm_sub_tendsto_zero
    (fun index => sequence (selection index))
    (fun index => core.restrict (selection index) (BoundedContinuousFunction.mkOfCompact limit))
    (core.embed (BoundedContinuousFunction.mkOfCompact limit)) referenceStrong differenceConverges

#print axioms EIGS.xiNativeL2_strong_of_uniform_subsequence

def XiNativeContinuousResolventProperties (system : EIGSData K)
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
    (normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
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
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass))),
    ∀ (step : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)
      (function : C(parameters.LimitSpace, ℝ)),
    let forcing := fun level => core.restrict level (BoundedContinuousFunction.mkOfCompact function)
    let solution := fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level)
    let closedSolution := QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable
      originalDense step stepPositive stepAtMostOne (core.embed (BoundedContinuousFunction.mkOfCompact function))
    ∃ limit : C(parameters.LimitSpace, ℝ),
      core.embed (BoundedContinuousFunction.mkOfCompact limit) = closedSolution ∧
      (∀ other : C(parameters.LimitSpace, ℝ),
        core.embed (BoundedContinuousFunction.mkOfCompact other) = closedSolution → other = limit) ∧
      ∃ selection : ℕ → ℕ, StrictMono selection ∧
        Tendsto (fun index => ‖fun vertex : XiVtx system (selection index) =>
          solution (selection index) vertex - limit (parameters.vertexEmbedding (selection index) vertex)‖)
          atTop (nhds 0)

theorem exists_xiNativeContinuousResolvent_of_rules (system : EIGSData K)
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
        atTop (nhds (normalization • resistanceVector)) ∧
      XiNativeContinuousResolventProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
      originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  dsimp only [XiNativeContinuousResolventProperties]
  refine ⟨originalDense, ?_⟩
  intro step stepPositive stepAtMostOne function
  let forcing := fun level => core.restrict level (BoundedContinuousFunction.mkOfCompact function)
  let solution := fun level => xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive (forcing level)
  have forcingBound (level : ℕ) :
      ‖fun vertex : XiVtx system level => forcing level vertex‖ ≤ ‖BoundedContinuousFunction.mkOfCompact function‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro vertex
    dsimp only [forcing]
    rw [xiSpeedL2Core_restrict_eq_finiteSpeedL2, xiFiniteSpeedL2_apply system rulesConnected]
    exact (BoundedContinuousFunction.mkOfCompact function).norm_coe_le_norm _
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (funext renormalizationEigenpair)
  obtain ⟨selection, selectionStrict, limit, uniformConvergence⟩ :
      ∃ selection : ℕ → ℕ, StrictMono selection ∧ ∃ limit : C(parameters.LimitSpace, ℝ),
        Tendsto (fun index => ‖fun vertex : XiVtx system (selection index) =>
          solution (selection index) vertex - limit (parameters.vertexEmbedding (selection index) vertex)‖)
          atTop (nhds 0) := by
    simpa only [solution, rateEquality] using
      xiNativeFiniteResolvent_exists_uniform_subsequence system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive mass normalization normalizationPositive step stepPositive forcing
        ‖BoundedContinuousFunction.mkOfCompact function‖ (norm_nonneg _) forcingBound
  have uniformStrong := xiNativeL2_strong_of_uniform_subsequence system rulesConnected parameters
    distanceGreaterThanOne mass selection selectionStrict solution limit uniformConvergence
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  have nativeStrong := xiNativeFiniteResolvent_strong_limit system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense step stepPositive stepAtMostOne
    forcing (core.embed (BoundedContinuousFunction.mkOfCompact function))
    (core.strong_restrict (BoundedContinuousFunction.mkOfCompact function))
  have sameClass := (core.reindex selection selectionStrict.tendsto_atTop).strong_limit_unique
    (fun index => solution (selection index)) _ _ uniformStrong
    (core.strong_reindex selection selectionStrict.tendsto_atTop nativeStrong)
  refine ⟨limit, sameClass, ?_, selection, selectionStrict, uniformConvergence⟩
  intro other otherClass
  apply xiContinuousL2Map_injective system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
  change core.embed (BoundedContinuousFunction.mkOfCompact other) =
    core.embed (BoundedContinuousFunction.mkOfCompact limit)
  exact otherClass.trans sameClass.symm

end
end EIGS

#print axioms EIGS.exists_xiNativeContinuousResolvent_of_rules
