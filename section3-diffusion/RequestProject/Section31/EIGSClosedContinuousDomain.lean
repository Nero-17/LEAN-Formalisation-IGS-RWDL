import RequestProject.Section31.EIGSClosedPointPositivity
import RequestProject.Section31.EIGSClosedRegularity
import RequestProject.Section31.EIGSL2EnergyConstants
import RequestProject.Section31.PositiveContinuousEvaluation

/-! Identification of actual completion point values on continuous members of
its closed domain. No continuous representative for every closed-domain element
is assumed. The later finite-trace bound gives equality of D intersect C with
the original continuous finite-energy domain. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31 UniformSpace
open scoped BoundedContinuousFunction

set_option maxHeartbeats 3000000
variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)

include rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance

theorem xiClosed_point_functional_eq_continuous (level : ℕ) (vertex : XiVtx system level) :
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    ∀ closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm,
    ∀ functional : QuadraticEnergySpace originalDomain originalForm nonnegative →L[ℝ] ℝ,
    (∀ values, functional values =
        ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm values.value).val
            (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)) →
    ∀ target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
    ∀ membership : xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair mass target ∈ QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
      QuadraticEnergySpace.completionFunctional originalDomain originalForm nonnegative functional
        ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm
          ⟨xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
            metricEigenpair mass target, membership⟩) =
      target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  dsimp only
  intro closable functional functionalAgreement target membership
  let continuousDomain := (QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative).comap
    (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass).toLinearMap
  let inclusion : continuousDomain →ₗ[ℝ] QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative :=
    { toFun := fun values => ⟨xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass values.val, values.property⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  let evaluation : continuousDomain →ₗ[ℝ] ℝ :=
    (QuadraticEnergySpace.completionFunctional originalDomain originalForm nonnegative functional).toLinearMap.comp
      ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm.toLinearMap.comp inclusion)
  have originalAgreement : ∀ original : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive,
      ∀ originalMembership : original.val ∈ continuousDomain,
      evaluation ⟨original.val, originalMembership⟩ = original.val
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex) := by
    intro original originalMembership
    let native := xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive original
    have liftEquality : (QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm
        (inclusion ⟨original.val, originalMembership⟩) =
        ((⟨native⟩ : QuadraticEnergySpace originalDomain originalForm nonnegative) :
          Completion (QuadraticEnergySpace originalDomain originalForm nonnegative)) := by
      apply QuadraticEnergySpace.completionMap_injective originalDomain originalForm nonnegative closable
      rw [QuadraticEnergySpace.completionMap_coe]
      exact congrArg Subtype.val
        ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).apply_symm_apply _)
    change QuadraticEnergySpace.completionFunctional originalDomain originalForm nonnegative functional
      ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm
        (inclusion ⟨original.val, originalMembership⟩)) = _
    rw [liftEquality, QuadraticEnergySpace.completionFunctional_coe, functionalAgreement]
    simp only [native, LinearEquiv.symm_apply_apply]
  have originalMember : ∀ original : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive,
      original.val ∈ continuousDomain := by
    intro original
    exact QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative
      (xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive original)
  apply positive_linearMap_eq_evaluation_of_uniform_core continuousDomain evaluation
    (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex) _ _ _ ⟨target, membership⟩
  · intro values valuesPositive
    apply xiClosed_point_functional_nonnegative system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level vertex
      closable functional functionalAgreement (inclusion values)
    have sameRepresentative := ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2)
      (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass)
      values.val
    filter_upwards [sameRepresentative] with point equality
    change 0 ≤ ((ContinuousMap.toLp 2
      (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass)
      ℝ values.val) : _ → ℝ) point
    rw [equality]
    exact valuesPositive point
  · intro value
    let original : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive :=
      ⟨ContinuousMap.const _ value, xiContinuousFiniteEnergyDomain_const system rulesConnected lengths lengthsPositive
        distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive value⟩
    exact ⟨originalMember original, originalAgreement original (originalMember original)⟩
  · intro values tolerance tolerancePositive
    obtain ⟨original, close⟩ := (xiClosedLpEnergy_regular_core system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair).1
        values.val tolerance tolerancePositive
    exact ⟨⟨original.val, originalMember original⟩, originalAgreement original (originalMember original), close⟩


theorem xiContinuous_mem_closedDomain_iff :
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    ∀ target : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
      xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass target ∈ QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative ↔
      target ∈ xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  dsimp only
  intro target
  constructor
  · intro membership
    let closedTarget : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative :=
      ⟨xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass target, membership⟩
    obtain ⟨sequence, completionLimit, energyLimit⟩ :=
      QuadraticEnergySpace.exists_original_completion_energy_approximation originalDomain originalForm nonnegative closable closedTarget
    let representatives := fun index => (xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm
        (sequence index).value
    have pointwiseLimit : ∀ level (vertex : XiVtx system level), Tendsto
        (fun index => (representatives index).val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)) atTop
        (nhds (target (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex))) := by
      intro level vertex
      obtain ⟨functional, functionalAgreement⟩ := exists_xiPoint_energy_functional system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level vertex
      have evaluationLimit := (QuadraticEnergySpace.completionFunctional originalDomain originalForm nonnegative functional).continuous.continuousAt.tendsto.comp
        completionLimit
      change Tendsto (fun index => QuadraticEnergySpace.completionFunctional originalDomain originalForm nonnegative functional
        (sequence index : Completion (QuadraticEnergySpace originalDomain originalForm nonnegative))) atTop
        (nhds (QuadraticEnergySpace.completionFunctional originalDomain originalForm nonnegative functional
          ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm closedTarget))) at evaluationLimit
      have targetValue := xiClosed_point_functional_eq_continuous system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level vertex closable functional
        functionalAgreement target membership
      change QuadraticEnergySpace.completionFunctional originalDomain originalForm nonnegative functional
        ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm closedTarget) = _ at targetValue
      simp only [QuadraticEnergySpace.completionFunctional_coe, targetValue] at evaluationLimit
      have pointValues : (fun index => functional (sequence index)) =
          fun index => (representatives index).val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex) :=
        funext fun index => functionalAgreement (sequence index)
      rw [pointValues] at evaluationLimit
      exact evaluationLimit
    change ∃ bound : ℝ, ∀ level,
      (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
        (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≤ bound
    refine ⟨QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable closedTarget, ?_⟩
    intro level
    have finiteEnergyLimit : Tendsto (fun index =>
        (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
          ((representatives index).val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)) atTop
        (nhds ((xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
          (target ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair))) := by
      simp only [xiUnionWeightedNetwork_energy_eq, Function.comp_apply]
      apply tendsto_finset_sum
      intro edge _
      exact ((pointwiseLimit level (XiTail system level edge)).sub
        (pointwiseLimit level (XiHead system level edge))).pow 2 |>.const_mul _
    apply le_of_tendsto_of_tendsto finiteEnergyLimit energyLimit
    apply Eventually.of_forall
    intro index
    have finite := (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).1
      (representatives index).property
    have comparison := ENNReal.toReal_mono finite
      (le_iSup (fun coarse => ENNReal.ofReal
        ((xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive coarse).energy
          ((representatives index).val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair))) level)
    have energyIdentity := xiContinuousLpEnergyQuadraticForm_of_continuous system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      (representatives index)
    rw [LinearEquiv.apply_symm_apply] at energyIdentity
    simpa only [ENNReal.toReal_ofReal (FiniteNetwork.energy_nonneg _ _), ← energyIdentity] using comparison
  · intro finite
    exact QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative
      (xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive ⟨target, finite⟩)
end EIGS

#print axioms EIGS.xiClosed_point_functional_eq_continuous

#print axioms EIGS.xiContinuous_mem_closedDomain_iff


