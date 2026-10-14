import RequestProject.Section31.EIGSAnchoredEnergyHilbert
import RequestProject.Section31.EIGSFiniteEnergyRestrictionEquiv
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! A bounded linear continuous extension operator from the actual anchored
energy Hilbert space into continuous functions on the same metric completion.
Its inverse restriction and boundedness are constructed, rather than assumed.
The final consumer supplies the restriction bijection from original rules.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31
noncomputable section
variable {K : ℕ}

theorem exists_xiAnchoredEnergy_continuous_linear_extension_of_bijective
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (anchor : XiVertexUnion system)
    (bijective : Function.Bijective (xiFiniteEnergyRestriction system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive)) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    ∃ extension : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive
        resistanceVector vectorPositive eigenpair anchor →L[ℝ]
      C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
      ∀ values vertex, extension values (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
        distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) = values.value.val vertex := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let restrictionEquiv := LinearEquiv.ofBijective
    (xiFiniteEnergyRestriction system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive) bijective
  let extensionLinear : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor →ₗ[ℝ]
      C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ) :=
    { toFun := fun values => (restrictionEquiv.symm values.value).val
      map_add' := by
        intro first second
        exact congrArg Subtype.val (map_add restrictionEquiv.symm first.value second.value)
      map_smul' := by
        intro scalar values
        exact congrArg Subtype.val (map_smul restrictionEquiv.symm scalar values.value) }
  have agreement : ∀ values vertex, extensionLinear values (xiCompletionUnionEmbedding system rulesConnected
      lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
      values.value.val vertex := by
    intro values vertex
    exact congrFun (congrArg Subtype.val (restrictionEquiv.apply_symm_apply values.value)) vertex
  let evaluations := xiAnchoredEnergyEvaluation system rulesConnected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair anchor
  have pointwiseBounded : ∀ values : XiAnchoredEnergyHilbert system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair anchor,
      ∃ bound : ℝ, ∀ vertex, ‖evaluations vertex values‖ ≤ bound := by
    intro values
    refine ⟨‖extensionLinear values‖, fun vertex => ?_⟩
    change ‖values.value.val vertex‖ ≤ ‖extensionLinear values‖
    rw [← agreement]
    exact (extensionLinear values).norm_coe_le_norm _
  obtain ⟨bound, boundValid⟩ := banach_steinhaus (g := evaluations) pointwiseBounded
  let positiveBound := |bound| + 1
  have boundPositive : 0 < positiveBound := by dsimp only [positiveBound]; positivity
  have enlarged : ∀ vertex, ‖evaluations vertex‖ ≤ positiveBound := by
    intro vertex
    exact (boundValid vertex).trans ((le_abs_self bound).trans (le_add_of_nonneg_right (by norm_num)))
  have normBound : ∀ values, ‖extensionLinear values‖ ≤ positiveBound * ‖values‖ := by
    intro values
    apply (ContinuousMap.norm_le (extensionLinear values) (mul_nonneg boundPositive.le (norm_nonneg values))).2
    intro point
    refine (xiCompletionUnionEmbedding_denseRange system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair).induction_on point
      (isClosed_le (extensionLinear values).continuous.norm continuous_const) ?_
    intro vertex
    rw [agreement]
    exact ((evaluations vertex).le_opNorm values).trans
      (mul_le_mul_of_nonneg_right (enlarged vertex) (norm_nonneg values))
  exact ⟨extensionLinear.mkContinuous positiveBound normBound, agreement⟩

theorem exists_xiAnchoredEnergy_continuous_linear_extension_of_rules
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (canonicalRateGreaterThanOne : 1 < system.resistanceSpectralRadius rulesConnected distancePositive) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    ∃ resistanceRate : ℝ, ∃ rateGreaterThanOne : 1 < resistanceRate,
    ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
    ∃ eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour,
    ∀ anchor : XiVertexUnion system,
    ∃ extension : XiAnchoredEnergyHilbert system rulesConnected resistanceRate (zero_lt_one.trans rateGreaterThanOne)
        resistanceVector vectorPositive eigenpair anchor →L[ℝ] C(parameters.LimitSpace, ℝ),
      ∀ values vertex, extension values (xiCompletionUnionEmbedding system rulesConnected parameters.lengths
        parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        (zero_lt_one.trans distanceGreaterThanOne) parameters.eigenpair vertex) = values.value.val vertex := by
  intro parameters distanceGreaterThanOne
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  obtain ⟨resistanceRate, rateGreaterThanOne, resistanceVector, vectorPositive, eigenpair, bijective⟩ :=
    exists_xiFiniteEnergyRestriction_bijective_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive canonicalRateGreaterThanOne
  refine ⟨resistanceRate, rateGreaterThanOne, resistanceVector, vectorPositive, eigenpair, fun anchor => ?_⟩
  exact exists_xiAnchoredEnergy_continuous_linear_extension_of_bijective system rulesConnected parameters.lengths
    parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
    resistanceRate (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive eigenpair anchor bijective

end
end EIGS

#print axioms EIGS.exists_xiAnchoredEnergy_continuous_linear_extension_of_rules
