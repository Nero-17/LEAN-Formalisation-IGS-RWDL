import RequestProject.Section31.EIGSNativeSupResolventEquation
import RequestProject.Section31.GeometricAffineApproximation

/-! The geometric approximation bound for the actual finite resolvent.
Only the short-time powers estimate remains as an explicit input here; the
native transition contraction, resolvent equation and sup bound are proved
internally. The original-rule short-time consumer supplies that input. -/

namespace EIGS

open MeasureTheory
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem xiNativeFiniteResolvent_sup_approximation
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)
    (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step) (forcing : XiVtx system level → ℝ)
    (error : ℝ) (errorNonnegative : 0 ≤ error) (count : ℕ)
    (shortTime : ∀ index < count,
      ‖(xiNativeSupTransition system rulesConnected level ^ index) forcing - forcing‖ ≤ error) :
    ‖fun vertex =>
      xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
        (xiFiniteSpeedL2 system mass level forcing) vertex - forcing vertex‖ ≤
      error + 2 * (step * xiNativeFiniteJumpRate system level resistanceRate normalization /
        (1 + step * xiNativeFiniteJumpRate system level resistanceRate normalization)) ^ count *
          ‖forcing‖ := by
  let rate := xiNativeFiniteJumpRate system level resistanceRate normalization
  let ratio := step * rate / (1 + step * rate)
  let solution : XiVtx system level → ℝ := fun vertex =>
    xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
        (xiFiniteSpeedL2 system mass level forcing) vertex
  have rateNonnegative' : 0 ≤ rate :=
    xiNativeFiniteJumpRate_nonnegative system level resistanceRate normalization
      rateNonnegative normalizationNonnegative
  have denominatorPositive : 0 < 1 + step * rate := by positivity
  have ratioNonnegative : 0 ≤ ratio := by dsimp [ratio]; positivity
  have ratioAtMostOne : ratio ≤ 1 := by
    apply (div_le_one denominatorPositive).mpr
    linarith
  have coefficientIdentity : (1 + step * rate)⁻¹ = 1 - ratio := by
    dsimp [ratio]
    field_simp [ne_of_gt denominatorPositive]
    ring
  have fixedPoint : solution = (1 - ratio) • forcing +
      ratio • xiNativeSupTransition system rulesConnected level solution := by
    rw [← coefficientIdentity]
    exact xiNativeFiniteResolvent_sup_affine_equation system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent mass level resistanceRate normalization rateNonnegative
        normalizationNonnegative step stepPositive forcing
  have solutionBound : ‖solution‖ ≤ ‖forcing‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg forcing)).mpr
    intro vertex
    have estimate := xiNativeFiniteResolvent_sup_bound system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent mass level resistanceRate normalization rateNonnegative
        normalizationNonnegative step stepPositive (xiFiniteSpeedL2 system mass level forcing) vertex
    change ‖solution vertex‖ ≤ ‖forcing‖
    rw [Real.norm_eq_abs]
    simpa only [xiFiniteSpeedL2_apply system rulesConnected] using estimate
  change ‖solution - forcing‖ ≤ error + 2 * ratio ^ count * ‖forcing‖
  exact IGS.Sec31.geometric_affine_fixedPoint_error
    (xiNativeSupTransition system rulesConnected level)
    (xiNativeSupTransition_norm_le_one system rulesConnected level)
    ratio ratioNonnegative ratioAtMostOne forcing solution fixedPoint
    ‖forcing‖ error (norm_nonneg forcing) errorNonnegative le_rfl solutionBound count shortTime

end
end EIGS

#print axioms EIGS.xiNativeFiniteResolvent_sup_approximation
