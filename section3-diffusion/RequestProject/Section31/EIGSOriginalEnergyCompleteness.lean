import RequestProject.Section31.LinearEquivEnergyCompleteness
import RequestProject.Section31.EIGSFiniteEnergyContinuousLinearExtension
import RequestProject.Section31.EIGSPointEnergyFunctional

/-! Completeness of the original continuous energy domain in its own original
energy-plus-L2 norm. The restriction bijection identifies it with the complete
anchored trace-energy Hilbert space. A proved point functional controls the
anchor in one direction; the actual bounded extension followed by the actual
L2 map controls the ambient norm in the reverse direction. No replacement norm
or closed-domain completeness is substituted for original-domain completeness.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31 MeasureTheory
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

variable (system : EIGSData K)
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
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)

local instance : CompactSpace (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
    (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) :=
  xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair

include rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance in
theorem xiOriginalEnergySpace_complete_of_anchored_extension
    (bijective : Function.Bijective (xiFiniteEnergyRestriction system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive))
    (extension : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
        eigenpair (xiVertexEmbedding system 0 true) →L[ℝ]
      C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (agreement : ∀ values vertex, extension values (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
      distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) = values.value.val vertex) :
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    CompleteSpace (QuadraticEnergySpace originalDomain originalForm nonnegative) := by
  let anchor := xiVertexEmbedding system 0 true
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  let continuousLpEquiv := xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let restrictionEquiv := LinearEquiv.ofBijective
    (xiFiniteEnergyRestriction system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) bijective
  let anchoredEquiv : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair anchor ≃ₗ[ℝ] xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive :=
    { AnchoredTraceEnergySpace.equivDomain _ _ _ _ with
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let energyEquiv := (((QuadraticEnergySpace.linearEquivDomain originalDomain originalForm nonnegative).trans
    continuousLpEquiv.symm).trans restrictionEquiv).trans anchoredEquiv.symm
  obtain ⟨evaluation, evaluationAgreement⟩ := exists_xiPoint_energy_functional system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
    metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair 0 true
  let ambient := (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
    metricEigenpair mass).comp extension
  change CompleteSpace (QuadraticEnergySpace originalDomain originalForm nonnegative)
  apply completeSpace_of_linearEquiv_energy_square_bounds energyEquiv evaluation ambient
  · intro values
    let continuous := continuousLpEquiv.symm values.value
    have anchoredIdentity := xiAnchoredEnergyHilbert_norm_sq system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor (energyEquiv values)
    change ‖energyEquiv values‖ ^ 2 =
      (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (continuous.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)).toReal +
      (continuous.val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair 0 true)) ^ 2 at anchoredIdentity
    have formIdentity := xiContinuousLpEnergyQuadraticForm_of_continuous system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair continuous
    change originalForm (continuousLpEquiv continuous) = _ at formIdentity
    rw [LinearEquiv.apply_symm_apply] at formIdentity
    have anchorIdentity := evaluationAgreement values
    change evaluation values = continuous.val (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair 0 true) at anchorIdentity
    rw [← formIdentity, ← anchorIdentity] at anchoredIdentity
    have originalIdentity := QuadraticEnergySpace.norm_sq originalDomain originalForm nonnegative values
    nlinarith [sq_nonneg ‖values.value.val‖]
  · intro values
    let original := energyEquiv.symm values
    let continuous := continuousLpEquiv.symm original.value
    have restrictionIdentity : xiFiniteEnergyRestriction system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive continuous =
        values.value := by
      have equality := congrArg AnchoredTraceEnergySpace.value (energyEquiv.apply_symm_apply values)
      exact equality
    have sameRestriction : continuous.val ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair = values.value.val :=
      congrArg Subtype.val restrictionIdentity
    have continuousAgreement : continuous.val = extension values := by
      apply ContinuousMap.ext
      intro point
      refine (xiCompletionUnionEmbedding_denseRange system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair).induction_on point
        (isClosed_eq continuous.val.continuous (extension values).continuous) ?_
      intro vertex
      rw [agreement]
      exact congrFun sameRestriction vertex
    have ambientIdentity : original.value.val = ambient values := by
      have equality := congrArg Subtype.val (continuousLpEquiv.apply_symm_apply original.value)
      change xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass continuous.val = original.value.val at equality
      rw [continuousAgreement] at equality
      exact equality.symm
    have formIdentity := xiContinuousLpEnergyQuadraticForm_of_continuous system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair continuous
    change originalForm (continuousLpEquiv continuous) = _ at formIdentity
    rw [LinearEquiv.apply_symm_apply, sameRestriction] at formIdentity
    have originalIdentity := QuadraticEnergySpace.norm_sq originalDomain originalForm nonnegative original
    rw [formIdentity, ambientIdentity] at originalIdentity
    have anchoredIdentity := xiAnchoredEnergyHilbert_norm_sq system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor values
    change ‖energyEquiv.symm values‖ ^ 2 ≤ ‖values‖ ^ 2 + ‖ambient values‖ ^ 2
    nlinarith [sq_nonneg (values.value.val anchor)]

end
end EIGS

#print axioms EIGS.xiOriginalEnergySpace_complete_of_anchored_extension
