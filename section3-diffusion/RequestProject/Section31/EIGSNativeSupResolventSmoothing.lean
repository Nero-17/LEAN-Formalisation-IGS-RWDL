import RequestProject.Section31.EIGSNativeSupResolventEquation

/-! The actual finite resolvent controls the native generator in supremum
norm, uniformly in the finite level. This supplies the generator input to
the Banach floor-clock comparisons on resolvent-smoothed functions. -/

namespace EIGS

open MeasureTheory
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiNativeFiniteResolvent_sup_generator_bound
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)
    (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step) (forcing : XiVtx system level → ℝ) :
    let solution : XiVtx system level → ℝ := fun vertex =>
      xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
        (xiFiniteSpeedL2 system mass level forcing) vertex
    ‖(xiNativeFiniteJumpRate system level resistanceRate normalization •
      (1 - xiNativeSupTransition system rulesConnected level)) solution‖ ≤ 2 * ‖forcing‖ / step := by
  let solution : XiVtx system level → ℝ := fun vertex =>
    xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (xiFiniteSpeedL2 system mass level forcing) vertex
  change ‖(xiNativeFiniteJumpRate system level resistanceRate normalization •
    (1 - xiNativeSupTransition system rulesConnected level)) solution‖ ≤ _
  have solutionBound : ‖solution‖ ≤ ‖forcing‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg forcing)).mpr
    intro vertex
    have estimate := xiNativeFiniteResolvent_sup_bound system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level resistanceRate normalization rateNonnegative normalizationNonnegative
      step stepPositive (xiFiniteSpeedL2 system mass level forcing) vertex
    change ‖solution vertex‖ ≤ ‖forcing‖
    rw [Real.norm_eq_abs]
    simpa only [xiFiniteSpeedL2_apply system rulesConnected] using estimate
  have generatorIdentity :
      (xiNativeFiniteJumpRate system level resistanceRate normalization •
        (1 - xiNativeSupTransition system rulesConnected level)) solution =
          step⁻¹ • (forcing - solution) := by
    funext vertex
    have equation := xiNativeFiniteResolvent_pointwise_equation system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level resistanceRate normalization rateNonnegative normalizationNonnegative
      step stepPositive (xiFiniteSpeedL2 system mass level forcing) vertex
    rw [xiFiniteSpeedL2_apply system rulesConnected] at equation
    change solution vertex + step * xiNativeFiniteJumpRate system level resistanceRate normalization *
      (solution vertex - ∑ target, transProb (XiSimpleGraph system level) vertex target * solution target) =
        forcing vertex at equation
    change xiNativeFiniteJumpRate system level resistanceRate normalization *
      (solution vertex - xiNativeSupTransition system rulesConnected level solution vertex) =
        step⁻¹ * (forcing vertex - solution vertex)
    rw [xiNativeSupTransition_apply]
    field_simp [ne_of_gt stepPositive]
    nlinarith [equation]
  rw [generatorIdentity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr stepPositive)]
  have differenceBound : ‖forcing - solution‖ ≤ 2 * ‖forcing‖ :=
    (norm_sub_le _ _).trans (by linarith)
  calc
    step⁻¹ * ‖forcing - solution‖ ≤ step⁻¹ * (2 * ‖forcing‖) :=
      mul_le_mul_of_nonneg_left differenceBound (inv_nonneg.mpr stepPositive.le)
    _ = 2 * ‖forcing‖ / step := by ring

end
end EIGS

#print axioms EIGS.xiNativeFiniteResolvent_sup_generator_bound
