import RequestProject.Section31.EIGSAnchoredEnergyHilbert
import RequestProject.Section31.EIGSFiniteEnergyRestrictionEquiv
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! Uniform evaluation bounds on the original metric completion in the
resistance-rate-greater-than-one regime. Actual skeleton evaluations are
continuous on the constructed anchored Hilbert space. Continuous extension
and compactness bound each individual function, so Banach-Steinhaus supplies
a uniform operator bound. Density then bounds the original continuous domain
at every completion point. All model data are supplied from the rules.
Candidate source: compilation is not claimed. -/

namespace EIGS
open IGS.Sec31
noncomputable section
variable {K : ℕ}

theorem exists_xiFiniteEnergy_uniform_evaluation_of_rules
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
    ∀ anchor : XiVertexUnion system, ∃ coefficient : ℝ, 0 < coefficient ∧
    ∀ function : xiContinuousFiniteEnergyDomain system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
        resistanceRate (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive,
      ‖function.val‖ ^ 2 ≤ coefficient *
        ((xiExtendedWeightedEnergy system resistanceRate (zero_lt_one.trans rateGreaterThanOne)
          resistanceVector vectorPositive
          (function.val ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceGreaterThanOne)
            parameters.eigenpair)).toReal +
        (function.val (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceGreaterThanOne)
          parameters.eigenpair anchor)) ^ 2) := by
  intro parameters distanceGreaterThanOne
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  obtain ⟨resistanceRate, rateGreaterThanOne, resistanceVector, vectorPositive, eigenpair, bijective⟩ :=
    exists_xiFiniteEnergyRestriction_bijective_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive canonicalRateGreaterThanOne
  refine ⟨resistanceRate, rateGreaterThanOne, resistanceVector, vectorPositive, eigenpair, ?_⟩
  intro anchor
  let evaluations := xiAnchoredEnergyEvaluation system rulesConnected resistanceRate
    (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive eigenpair anchor
  have pointwiseBounded : ∀ values : XiAnchoredEnergyHilbert system rulesConnected resistanceRate
      (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive eigenpair anchor,
      ∃ bound : ℝ, ∀ vertex, ‖evaluations vertex values‖ ≤ bound := by
    intro values
    obtain ⟨function, restriction⟩ := bijective.2 values.value
    refine ⟨‖function.val‖, fun vertex => ?_⟩
    have agreement := congrFun (congrArg Subtype.val restriction) vertex
    change function.val (xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceGreaterThanOne)
      parameters.eigenpair vertex) = values.value.val vertex at agreement
    change ‖values.value.val vertex‖ ≤ ‖function.val‖
    rw [← agreement]
    exact function.val.norm_coe_le_norm _
  obtain ⟨bound, boundValid⟩ := banach_steinhaus (g := evaluations) pointwiseBounded
  let positiveBound := |bound| + 1
  have boundPositive : 0 < positiveBound := by dsimp only [positiveBound]; positivity
  have enlarged : ∀ vertex, ‖evaluations vertex‖ ≤ positiveBound := by
    intro vertex
    exact (boundValid vertex).trans ((le_abs_self bound).trans (le_add_of_nonneg_right (by norm_num)))
  refine ⟨positiveBound ^ 2, pow_pos boundPositive _, ?_⟩
  intro function
  let values : XiAnchoredEnergyHilbert system rulesConnected resistanceRate
      (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive eigenpair anchor :=
    ⟨xiFiniteEnergyRestriction system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
      resistanceRate (zero_lt_one.trans rateGreaterThanOne) resistanceVector vectorPositive function⟩
  have pointBound : ∀ point, |function.val point| ≤ positiveBound * ‖values‖ := by
    intro point
    refine (xiCompletionUnionEmbedding_denseRange system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceGreaterThanOne)
      parameters.eigenpair).induction_on point
      (isClosed_le function.val.continuous.abs continuous_const) ?_
    intro vertex
    have applied := (evaluations vertex).le_opNorm values
    exact applied.trans (mul_le_mul_of_nonneg_right (enlarged vertex) (norm_nonneg values))
  have normBound : ‖function.val‖ ≤ positiveBound * ‖values‖ := by
    apply (ContinuousMap.norm_le function.val (mul_nonneg boundPositive.le (norm_nonneg values))).mpr
    intro point
    simpa only [Real.norm_eq_abs] using pointBound point
  have squareBound := (sq_le_sq₀ (norm_nonneg function.val)
    (mul_nonneg boundPositive.le (norm_nonneg values))).2 normBound
  rw [mul_pow, xiAnchoredEnergyHilbert_norm_sq] at squareBound
  exact squareBound

end
end EIGS

#print axioms EIGS.exists_xiFiniteEnergy_uniform_evaluation_of_rules
