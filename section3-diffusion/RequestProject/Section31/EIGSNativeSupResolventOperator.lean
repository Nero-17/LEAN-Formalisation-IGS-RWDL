import RequestProject.Section31.EIGSNativeSupResolventEquation

/-! The actual finite resolvent is a supremum-norm contraction on vertex
functions. Evaluation conjugates the already constructed native speed L²
operator. The inverse and commutation identities are transported from that
actual operator; no commutation or resolvent identity is assumed. -/

namespace EIGS

open MeasureTheory
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}
variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)
    (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step)

def xiNativeSupResolvent :
    (XiVtx system level → ℝ) →L[ℝ] (XiVtx system level → ℝ) :=
  let evaluation := xiNativeEvaluationLinearEquiv system rulesConnected mass level
  let linear := evaluation.toLinearMap.comp
    ((xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive).toLinearMap.comp
      evaluation.symm.toLinearMap)
  linear.mkContinuous 1 (fun forcing => by
    simp only [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg forcing)).mpr
    intro vertex
    change ‖xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (xiFiniteSpeedL2 system mass level forcing) vertex‖ ≤ ‖forcing‖
    rw [Real.norm_eq_abs]
    have estimate := xiNativeFiniteResolvent_sup_bound system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level resistanceRate normalization rateNonnegative normalizationNonnegative
      step stepPositive (xiFiniteSpeedL2 system mass level forcing) vertex
    simpa only [xiFiniteSpeedL2_apply system rulesConnected] using estimate)

theorem xiNativeSupResolvent_apply (forcing : XiVtx system level → ℝ) (vertex : XiVtx system level) :
    xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing vertex =
    xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (xiFiniteSpeedL2 system mass level forcing) vertex := rfl

theorem xiNativeSupResolvent_norm_le_one :
    ‖xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro forcing
  simp only [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg forcing)).mpr
  intro vertex
  rw [xiNativeSupResolvent_apply, Real.norm_eq_abs]
  have estimate := xiNativeFiniteResolvent_sup_bound system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level resistanceRate normalization rateNonnegative normalizationNonnegative
    step stepPositive (xiFiniteSpeedL2 system mass level forcing) vertex
  simpa only [xiFiniteSpeedL2_apply system rulesConnected] using estimate

theorem xiNativeSupResolvent_evaluation
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (xiNativeEvaluationLinearEquiv system rulesConnected mass level values) =
    xiNativeEvaluationLinearEquiv system rulesConnected mass level
      (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive values) := by
  funext vertex
  rw [xiNativeSupResolvent_apply]
  change xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
    (xiFiniteSpeedL2 system mass level (fun vertex => values vertex)) vertex = _
  rw [xiFiniteSpeedL2_representative]
  rfl

def xiNativeSupGenerator :
    (XiVtx system level → ℝ) →L[ℝ] (XiVtx system level → ℝ) :=
  xiNativeFiniteJumpRate system level resistanceRate normalization •
    (1 - xiNativeSupTransition system rulesConnected level)

theorem xiNativeSupGenerator_evaluation
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    xiNativeEvaluationLinearEquiv system rulesConnected mass level
      (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization values) =
    xiNativeSupGenerator system rulesConnected level resistanceRate normalization
      (xiNativeEvaluationLinearEquiv system rulesConnected mass level values) := by
  change (xiNativeEvaluationLinearEquiv system rulesConnected mass level)
    (xiNativeFiniteJumpRate system level resistanceRate normalization •
      (values - xiNativeRandomWalk system rulesConnected mass level values)) = _
  rw [map_smul, map_sub]
  funext vertex
  change xiNativeFiniteJumpRate system level resistanceRate normalization *
    (values vertex - xiNativeRandomWalk system rulesConnected mass level values vertex) =
    xiNativeFiniteJumpRate system level resistanceRate normalization *
      (values vertex - xiNativeSupTransition system rulesConnected level (fun vertex => values vertex) vertex)
  rw [xiNativeRandomWalk_apply, xiNativeSupTransition_apply]

theorem xiNativeSupResolvent_equation (forcing : XiVtx system level → ℝ) :
    xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing +
    step • xiNativeSupGenerator system rulesConnected level resistanceRate normalization
      (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing) = forcing := by
  let evaluation := xiNativeEvaluationLinearEquiv system rulesConnected mass level
  have transported := congrArg evaluation
    (((xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive).1
      (evaluation.symm forcing)).1)
  dsimp only [evaluation] at transported
  simpa only [map_add, map_smul, xiNativeSupGenerator_evaluation,
    ← xiNativeSupResolvent_evaluation, LinearEquiv.apply_symm_apply] using transported

theorem xiNativeSupResolvent_inverse (values : XiVtx system level → ℝ) :
    xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (values + step • xiNativeSupGenerator system rulesConnected level resistanceRate normalization values) = values := by
  let evaluation := xiNativeEvaluationLinearEquiv system rulesConnected mass level
  have transported := congrArg evaluation
    (xiNativeFiniteResolvent_inverse system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (evaluation.symm values))
  dsimp only [evaluation] at transported
  simpa only [map_add, map_smul, xiNativeSupGenerator_evaluation,
    ← xiNativeSupResolvent_evaluation, LinearEquiv.apply_symm_apply] using transported

theorem xiNativeSupGenerator_resolvent_apply (values : XiVtx system level → ℝ) :
    xiNativeSupGenerator system rulesConnected level resistanceRate normalization
      (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive values) =
    xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (xiNativeSupGenerator system rulesConnected level resistanceRate normalization values) := by
  let evaluation := xiNativeEvaluationLinearEquiv system rulesConnected mass level
  have transported := congrArg evaluation
    (xiNativeFiniteGenerator_resolvent_apply system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (evaluation.symm values))
  dsimp only [evaluation] at transported
  simpa only [xiNativeSupGenerator_evaluation, ← xiNativeSupResolvent_evaluation,
    LinearEquiv.apply_symm_apply] using transported

theorem xiNativeSupGenerator_resolvent_commute :
    Commute (xiNativeSupGenerator system rulesConnected level resistanceRate normalization)
      (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive) := by
  apply (commute_iff_eq _ _).mpr
  apply ContinuousLinearMap.ext
  intro values
  exact xiNativeSupGenerator_resolvent_apply system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive values

theorem xiNativeSupGenerator_resolvent_graph (forcing : XiVtx system level → ℝ) :
    xiNativeSupGenerator system rulesConnected level resistanceRate normalization
      (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing) =
    step⁻¹ • (forcing - xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing) := by
  let evaluation := xiNativeEvaluationLinearEquiv system rulesConnected mass level
  have transported := congrArg evaluation
    (xiNativeFiniteGenerator_resolvent_graph system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (evaluation.symm forcing))
  dsimp only [evaluation] at transported
  simpa only [map_smul, map_sub, xiNativeSupGenerator_evaluation,
    ← xiNativeSupResolvent_evaluation, LinearEquiv.apply_symm_apply] using transported

theorem xiNativeSupYosidaGenerator_apply (values : XiVtx system level → ℝ) :
    IGS.Sec31.BoundedYosida.generator
      (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive) step values =
    xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (xiNativeSupGenerator system rulesConnected level resistanceRate normalization values) := by
  change step⁻¹ • (values - xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive values) = _
  rw [← xiNativeSupGenerator_resolvent_graph system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive values]
  exact xiNativeSupGenerator_resolvent_apply system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive values

theorem xiNativeSupGenerator_yosida_commute :
    Commute (xiNativeSupGenerator system rulesConnected level resistanceRate normalization)
      (IGS.Sec31.BoundedYosida.generator
        (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive) step) := by
  exact ((Commute.one_right _).sub_right
    (xiNativeSupGenerator_resolvent_commute system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)).smul_right step⁻¹

end
end EIGS

#print axioms EIGS.xiNativeSupResolvent_apply
#print axioms EIGS.xiNativeSupResolvent_norm_le_one
#print axioms EIGS.xiNativeSupResolvent_evaluation
#print axioms EIGS.xiNativeSupGenerator_evaluation
#print axioms EIGS.xiNativeSupResolvent_equation
#print axioms EIGS.xiNativeSupResolvent_inverse
#print axioms EIGS.xiNativeSupGenerator_resolvent_apply
#print axioms EIGS.xiNativeSupGenerator_resolvent_commute
#print axioms EIGS.xiNativeSupGenerator_resolvent_graph
#print axioms EIGS.xiNativeSupYosidaGenerator_apply
#print axioms EIGS.xiNativeSupGenerator_yosida_commute
