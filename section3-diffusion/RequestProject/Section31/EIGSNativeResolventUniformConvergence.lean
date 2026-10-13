import RequestProject.Section31.EIGSNativeResolventContinuousIdentification
import RequestProject.Section31.EIGSNativeResolventReindexedSubsequence

/-! Full-sequence uniform convergence of actual finite resolvents of continuous
forcing. Every selected set of levels admits a further uniform limit; the
actual Strong closed-resolvent limit and full support identify it uniquely.
No subsequential compactness or target uniform convergence is assumed in the
original-rule result. Steps remain in the range 0 < step ≤ 1. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

def XiNativeUniformResolventProperties (system : EIGSData K)
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
      Tendsto (fun level => ‖fun vertex : XiVtx system level =>
        solution level vertex - limit (parameters.vertexEmbedding level vertex)‖) atTop (nhds 0)

theorem xiNativeUniformResolventProperties_of_continuous (system : EIGSData K)
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
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector)))
    (continuousProperties : XiNativeContinuousResolventProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive) :
    XiNativeUniformResolventProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
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
  dsimp only [XiNativeContinuousResolventProperties, XiNativeUniformResolventProperties]
    at continuousProperties ⊢
  obtain ⟨originalDense, continuousProperties⟩ := continuousProperties
  refine ⟨originalDense, ?_⟩
  intro step stepPositive stepAtMostOne function
  obtain ⟨limit, sameClass, unique, uniformSubsequence⟩ :=
    continuousProperties step stepPositive stepAtMostOne function
  refine ⟨limit, sameClass, unique, ?_⟩
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
  rw [← sameClass] at nativeStrong
  apply tendsto_of_every_strict_subsequence_has_further_limit
    (fun level => ‖fun vertex : XiVtx system level =>
      solution level vertex - limit (parameters.vertexEmbedding level vertex)‖) 0
  intro levels levelsStrict
  have rateEquality := system.resistanceSpectralRadius_eq_of_positive_eigenpair rulesConnected distancePositive
    ratePositive vectorPositive (funext renormalizationEigenpair)
  obtain ⟨selection, selectionStrict, other, otherUniform⟩ :
      ∃ selection : ℕ → ℕ, StrictMono selection ∧ ∃ other : C(parameters.LimitSpace, ℝ),
        Tendsto (fun index => ‖fun vertex : XiVtx system (levels (selection index)) =>
          solution (levels (selection index)) vertex - other (parameters.vertexEmbedding (levels (selection index)) vertex)‖)
          atTop (nhds 0) := by
    simpa only [solution, rateEquality] using
      xiNativeFiniteResolvent_exists_uniform_subsequence_along system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive mass normalization normalizationPositive step stepPositive forcing
        ‖BoundedContinuousFunction.mkOfCompact function‖ (norm_nonneg _) forcingBound levels levelsStrict
  have composedStrict : StrictMono (levels ∘ selection) := levelsStrict.comp selectionStrict
  have otherStrong := xiNativeL2_strong_of_uniform_subsequence system rulesConnected parameters
    distanceGreaterThanOne mass (levels ∘ selection) composedStrict solution other otherUniform
  have selectedNativeStrong := core.strong_reindex (levels ∘ selection) composedStrict.tendsto_atTop
    (sequence := solution) (limit := core.embed (BoundedContinuousFunction.mkOfCompact limit)) nativeStrong
  have otherClass := (core.reindex (levels ∘ selection) composedStrict.tendsto_atTop).strong_limit_unique
    (fun index => solution ((levels ∘ selection) index)) _ _ otherStrong selectedNativeStrong
  have otherEquality : other = limit := unique other (otherClass.trans sameClass)
  refine ⟨selection, ?_⟩
  simpa only [otherEquality] using otherUniform

theorem exists_xiNativeUniformResolvent_of_rules (system : EIGSData K)
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
      XiNativeUniformResolventProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, continuousProperties⟩ :=
    exists_xiNativeContinuousResolvent_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiNativeUniformResolventProperties_of_continuous system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive normalizedConvergence continuousProperties

end
end EIGS

#print axioms EIGS.xiNativeUniformResolventProperties_of_continuous
#print axioms EIGS.exists_xiNativeUniformResolvent_of_rules
