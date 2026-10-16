import RequestProject.Section31.EIGSMetricOfRules
import RequestProject.Section31.EIGSHarmonicBoundaryL2
import RequestProject.Section31.EIGSContinuousProjectionPythagoras
import RequestProject.Section31.EIGSPointEnergyFunctional
import RequestProject.Section31.EIGSL2ClosabilityWithoutPrimitive

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology UniformSpace
noncomputable section
set_option maxHeartbeats 8000000
variable {K : ℕ}

/-- Exact harmonic trace and Pythagoras on the entire actual closed form domain.
The evaluations are extensions in the energy norm; no continuous representative
of a closed-domain target is required. -/
theorem exists_xiClosedHarmonicTrace_pythagoras
    (system : EIGSData K)
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
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) :
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    ∀ closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm,
    ∀ level : ℕ,
      ∃ evaluation : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative →ₗ[ℝ] (XiVtx system level → ℝ),
      ∃ harmonic : (XiVtx system level → ℝ) →ₗ[ℝ] originalDomain,
        (∀ values : originalDomain, ∀ vertex,
          evaluation ⟨values.val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative values⟩ vertex =
            ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm values).val
              (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
                (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)) ∧
        (∀ values vertex,
          ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm (harmonic values)).val
            (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
          xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level values vertex) ∧
        ∀ target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
          let projection : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative :=
            ⟨(harmonic (evaluation target)).val,
              QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative (harmonic (evaluation target))⟩
          (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable projection =
            (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy (evaluation target)) ∧
          (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target =
            QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable projection +
            QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable (target - projection)) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let energyEquiv := xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  dsimp only
  intro closable level
  obtain ⟨extensionMap, extensionAgreement, _, _⟩ := exists_xiHarmonic_boundary_L2_control system rulesConnected
    lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass distancePositive oneColourDistance
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level
  have extensionEnergy (values : XiVtx system level → ℝ) :
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (extensionMap values ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) =
      ENNReal.ofReal ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy values) := by
    apply xiContinuousHarmonic_extended_energy system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair level values (extensionMap values)
    intro offset vertex
    exact (extensionAgreement values (xiVertexEmbedding system (level + offset) vertex)).trans
      (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair level values offset vertex)
  let continuousLift : (XiVtx system level → ℝ) →ₗ[ℝ]
      xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive :=
    extensionMap.codRestrict _ (fun values =>
      (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).2
        (ne_of_eq_of_ne (extensionEnergy values) ENNReal.ofReal_ne_top))
  let harmonic : (XiVtx system level → ℝ) →ₗ[ℝ] originalDomain := energyEquiv.toLinearMap.comp continuousLift
  let energyLift : (XiVtx system level → ℝ) →L[ℝ] QuadraticEnergySpace originalDomain originalForm nonnegative :=
    ((QuadraticEnergySpace.linearEquivDomain originalDomain originalForm nonnegative).symm.toLinearMap.comp harmonic).toContinuousLinearMap
  choose functional functionalAgreement using fun vertex : XiVtx system level =>
    exists_xiPoint_energy_functional system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level vertex
  let trace : Completion (QuadraticEnergySpace originalDomain originalForm nonnegative) →L[ℝ] (XiVtx system level → ℝ) :=
    ContinuousLinearMap.pi (fun vertex => QuadraticEnergySpace.completionFunctional originalDomain originalForm nonnegative (functional vertex))
  let evaluation := trace.toLinearMap.comp (QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm.toLinearMap
  let projection : Completion (QuadraticEnergySpace originalDomain originalForm nonnegative) →L[ℝ]
      Completion (QuadraticEnergySpace originalDomain originalForm nonnegative) :=
    Completion.toComplL.comp (energyLift.comp trace)
  have traceCoe (values : QuadraticEnergySpace originalDomain originalForm nonnegative) (vertex : XiVtx system level) :
      trace (values : Completion (QuadraticEnergySpace originalDomain originalForm nonnegative)) vertex =
      (energyEquiv.symm values.value).val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex) := by
    exact (QuadraticEnergySpace.completionFunctional_coe originalDomain originalForm nonnegative (functional vertex) values).trans
      (functionalAgreement vertex values)
  have harmonicEnergy (values : XiVtx system level → ℝ) : originalForm (harmonic values) =
      (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy values := by
    change originalForm (energyEquiv (continuousLift values)) = _
    rw [xiContinuousLpEnergyQuadraticForm_of_continuous]
    change (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (extensionMap values ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal = _
    rw [extensionEnergy]
    exact ENNReal.toReal_ofReal ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy_nonneg values)
  have corePythagoras (values : originalDomain) : originalForm values =
      originalForm (harmonic (fun vertex => (energyEquiv.symm values).val
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex))) +
      originalForm (values - harmonic (fun vertex => (energyEquiv.symm values).val
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex))) := by
    let target := xiContinuousEnergyToUnionDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive (energyEquiv.symm values)
    let boundary := fun vertex => (energyEquiv.symm values).val
      (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)
    let lifted := xiContinuousEnergyToUnionDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive (continuousLift boundary)
    have boundaryAgreement (vertex : XiVtx system level) : target.val (xiVertexEmbedding system level vertex) =
        lifted.val (xiVertexEmbedding system level vertex) := by
      exact ((extensionAgreement boundary (xiVertexEmbedding system level vertex)).trans
        (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
          renormalizationEigenpair level boundary 0 vertex)).symm
    have liftedCore : lifted ∈ xiHarmonicCoreAt system resistanceRate ratePositive resistanceVector vectorPositive level := by
      change xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (extensionMap boundary ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) = _
      rw [extensionEnergy]
      congr 1
      apply congrArg (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
      funext vertex
      exact boundaryAgreement vertex
    have identity := xiHarmonicCoreAt_energy_pythagoras system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair level lifted target liftedCore boundaryAgreement
    change originalForm values = originalForm (harmonic boundary) + originalForm (values - harmonic boundary)
    have liftInverse (boundary : XiVtx system level → ℝ) : energyEquiv.symm (harmonic boundary) = continuousLift boundary :=
      energyEquiv.symm_apply_apply (continuousLift boundary)
    have formValue (values : originalDomain) : originalForm values =
        (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
          (xiContinuousEnergyToUnionDomain system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
            (energyEquiv.symm values))).toReal := rfl
    rw [formValue values, formValue (harmonic boundary), formValue (values - harmonic boundary)]
    simp only [map_sub, liftInverse]
    exact identity
  have completionEnergyCoe (values : QuadraticEnergySpace originalDomain originalForm nonnegative) :
      ‖(values : Completion (QuadraticEnergySpace originalDomain originalForm nonnegative))‖ ^ 2 -
        ‖QuadraticEnergySpace.completionMap originalDomain originalForm nonnegative
          (values : Completion (QuadraticEnergySpace originalDomain originalForm nonnegative))‖ ^ 2 =
      originalForm values.value := by
    have normIdentity := QuadraticEnergySpace.norm_sq originalDomain originalForm nonnegative values
    have mapIdentity := QuadraticEnergySpace.completionMap_coe originalDomain originalForm nonnegative values
    have completionNorm := Completion.norm_coe values
    rw [completionNorm, mapIdentity]
    linarith only [normIdentity]
  have completionPythagoras (point : Completion (QuadraticEnergySpace originalDomain originalForm nonnegative)) :
      ‖point‖ ^ 2 - ‖QuadraticEnergySpace.completionMap originalDomain originalForm nonnegative point‖ ^ 2 =
      (‖projection point‖ ^ 2 - ‖QuadraticEnergySpace.completionMap originalDomain originalForm nonnegative (projection point)‖ ^ 2) +
      (‖point - projection point‖ ^ 2 - ‖QuadraticEnergySpace.completionMap originalDomain originalForm nonnegative (point - projection point)‖ ^ 2) := by
    induction point using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih values =>
      have traceEquality : trace (values : Completion (QuadraticEnergySpace originalDomain originalForm nonnegative)) =
          fun vertex => (energyEquiv.symm values.value).val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex) := funext (traceCoe values)
      simp only [projection, ContinuousLinearMap.comp_apply, traceEquality, Completion.coe_toComplL]
      change ‖(values : Completion (QuadraticEnergySpace originalDomain originalForm nonnegative))‖ ^ 2 -
          ‖QuadraticEnergySpace.completionMap originalDomain originalForm nonnegative (values : Completion (QuadraticEnergySpace originalDomain originalForm nonnegative))‖ ^ 2 = _
      rw [← Completion.coe_sub]
      have valueEnergy := completionEnergyCoe values
      have liftedEnergy := completionEnergyCoe (energyLift (fun vertex => (energyEquiv.symm values.value).val
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)))
      have residualEnergy := completionEnergyCoe (values - energyLift (fun vertex => (energyEquiv.symm values.value).val
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)))
      rw [valueEnergy, liftedEnergy, residualEnergy]
      exact corePythagoras values.value
  refine ⟨evaluation, harmonic, ?_, ?_, ?_⟩
  · intro values vertex
    have inverseValue : (QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm
        ⟨values.val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative values⟩ =
        ((⟨values⟩ : QuadraticEnergySpace originalDomain originalForm nonnegative) : Completion (QuadraticEnergySpace originalDomain originalForm nonnegative)) := by
      apply QuadraticEnergySpace.completionMap_injective originalDomain originalForm nonnegative closable
      rw [QuadraticEnergySpace.completionMap_coe]
      exact congrArg Subtype.val ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).apply_symm_apply _)
    change trace ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm _) vertex = _
    rw [inverseValue]
    exact traceCoe ⟨values⟩ vertex
  · intro values vertex
    change (energyEquiv.symm (harmonic values)).val _ = _
    have liftInverse : energyEquiv.symm (harmonic values) = continuousLift values :=
      energyEquiv.symm_apply_apply (continuousLift values)
    rw [liftInverse]
    exact extensionAgreement values vertex
  · intro target
    constructor
    · rw [QuadraticEnergySpace.closedForm_extends]
      exact harmonicEnergy (evaluation target)
    · have projectionInverse : (QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm
          ⟨(harmonic (evaluation target)).val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative (harmonic (evaluation target))⟩ =
          projection ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm target) := by
        apply QuadraticEnergySpace.completionMap_injective originalDomain originalForm nonnegative closable
        change _ = QuadraticEnergySpace.completionMap originalDomain originalForm nonnegative
          ((energyLift (evaluation target) : QuadraticEnergySpace originalDomain originalForm nonnegative) : Completion (QuadraticEnergySpace originalDomain originalForm nonnegative))
        rw [QuadraticEnergySpace.completionMap_coe]
        exact congrArg Subtype.val ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).apply_symm_apply _)
      have targetImage : QuadraticEnergySpace.completionMap originalDomain originalForm nonnegative
          ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm target) = target.val :=
        congrArg Subtype.val ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).apply_symm_apply target)
      have projectionImage : QuadraticEnergySpace.completionMap originalDomain originalForm nonnegative
          (projection ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm target)) =
          (harmonic (evaluation target)).val := by
        change QuadraticEnergySpace.completionMap originalDomain originalForm nonnegative
          ((energyLift (evaluation target) : QuadraticEnergySpace originalDomain originalForm nonnegative) :
            Completion (QuadraticEnergySpace originalDomain originalForm nonnegative)) = _
        rw [QuadraticEnergySpace.completionMap_coe]
        rfl
      rw [QuadraticEnergySpace.closedForm_value, QuadraticEnergySpace.closedForm_value, QuadraticEnergySpace.closedForm_value,
        map_sub, projectionInverse]
      have identity := completionPythagoras ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm target)
      simpa only [map_sub, targetImage, projectionImage] using identity

end
end EIGS
#print axioms EIGS.exists_xiClosedHarmonicTrace_pythagoras

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology UniformSpace
noncomputable section
set_option maxHeartbeats 8000000
variable {K : ℕ}
/-- Exact harmonic trace and Pythagoras on the entire actual closed form domain.
The evaluations are extensions in the energy norm; no continuous representative
of a closed-domain target is required. -/
theorem exists_xiClosedHarmonicTrace_pythagoras_of_rules
    (system : EIGSData K)
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
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) :
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair sequence energyCauchy (by simpa using ambientZero.norm)
    ∀ level : ℕ,
      ∃ evaluation : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative →ₗ[ℝ] (XiVtx system level → ℝ),
      ∃ harmonic : (XiVtx system level → ℝ) →ₗ[ℝ] originalDomain,
        (∀ values : originalDomain, ∀ vertex,
          evaluation ⟨values.val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative values⟩ vertex =
            ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm values).val
              (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
                (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)) ∧
        (∀ values vertex,
          ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm (harmonic values)).val
            (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
          xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level values vertex) ∧
        (∀ values, evaluation
          ⟨(harmonic values).val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative (harmonic values)⟩ = values) ∧
        (∀ values (target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative),
          evaluation target = values →
          QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable
            ⟨(harmonic values).val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative (harmonic values)⟩ ≤
          QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target) ∧
        ∀ target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
          let projection : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative :=
            ⟨(harmonic (evaluation target)).val,
              QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative (harmonic (evaluation target))⟩
          (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable projection =
            (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy (evaluation target)) ∧
          (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target =
            QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable projection +
            QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable (target - projection)) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let energyEquiv := xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair sequence energyCauchy (by simpa using ambientZero.norm)
  dsimp only
  intro level
  obtain ⟨evaluation, harmonic, evaluationAgreement, harmonicAgreement, identity⟩ :=
    exists_xiClosedHarmonicTrace_pythagoras system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair closable level
  have rightInverse (values : XiVtx system level → ℝ) : evaluation
      ⟨(harmonic values).val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative (harmonic values)⟩ = values := by
    funext vertex
    rw [evaluationAgreement]
    exact (harmonicAgreement values (xiVertexEmbedding system level vertex)).trans
      (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair level values 0 vertex)
  refine ⟨evaluation, harmonic, evaluationAgreement, harmonicAgreement, rightInverse, ?_, identity⟩
  intro values target sameTrace
  have decomposition := (identity target).2
  rw [sameTrace] at decomposition
  have residualNonnegative := QuadraticEnergySpace.closedForm_nonnegative originalDomain originalForm nonnegative closable
    (target - ⟨(harmonic values).val,
      QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative (harmonic values)⟩)
  linarith
end
end EIGS
#print axioms EIGS.exists_xiClosedHarmonicTrace_pythagoras_of_rules




namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology UniformSpace
noncomputable section
set_option maxHeartbeats 8000000
variable {K : ℕ}

theorem exists_xiClosedHarmonicTrace_pythagoras_constructed_of_rules
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
        (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
        renormalizationEigenpair sequence energyCauchy (by simpa using ambientZero.norm)
    ∀ level : ℕ,
      ∃ evaluation : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative →ₗ[ℝ] (XiVtx system level → ℝ),
      ∃ harmonic : (XiVtx system level → ℝ) →ₗ[ℝ] originalDomain,
        (∀ values : originalDomain, ∀ vertex,
          evaluation ⟨values.val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative values⟩ vertex =
            ((xiContinuousEnergyLpEquiv system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm values).val
              (xiCompletionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
                (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair level vertex)) ∧
        (∀ values vertex,
          ((xiContinuousEnergyLpEquiv system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
            distanceGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm (harmonic values)).val
            (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair vertex) =
          xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair level values vertex) ∧
        (∀ values, evaluation
          ⟨(harmonic values).val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative (harmonic values)⟩ = values) ∧
        (∀ values (target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative),
          evaluation target = values →
          QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable
            ⟨(harmonic values).val, QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative (harmonic values)⟩ ≤
          QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target) ∧
        ∀ target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
          let projection : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative :=
            ⟨(harmonic (evaluation target)).val,
              QuadraticEnergySpace.original_mem_closedDomain originalDomain originalForm nonnegative (harmonic (evaluation target))⟩
          (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable projection =
            (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy (evaluation target)) ∧
          (QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable target =
            QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable projection +
            QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable (target - projection)) := by
  classical
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  have coloursPositive : 0 < K := lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt
  obtain ⟨resistanceVector, resistanceRate, vectorPositive, ratePositive, _, eigenpair⟩ :=
    (system.connectedRuleSystem rulesConnected).distance_positive_eigenpair coloursPositive distancePositive
  have renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour :=
    fun colour => congrFun eigenpair colour
  dsimp only
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair, ?_⟩
  exact exists_xiClosedHarmonicTrace_pythagoras_of_rules system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair

end
end EIGS
#print axioms EIGS.exists_xiClosedHarmonicTrace_pythagoras_constructed_of_rules

