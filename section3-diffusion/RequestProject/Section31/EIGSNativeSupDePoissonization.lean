import RequestProject.Section31.EIGSNativeSupSemigroupComparison
import RequestProject.Section31.EIGSNativeSupResolventSmoothing

/-! Actual finite-graph de-Poissonization after resolvent smoothing, in the
vertex supremum norm. The error is uniform over every starting vertex.
Both an individual observation time and differences of absolute clocks
are covered; the latter are the clocks used in finite-dimensional laws. -/

namespace EIGS

open IGS.Sec31 Filter Topology
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
    (ratePositive : 0 < resistanceRate) (normalizationPositive : 0 < normalization)
    (step : ℝ) (stepPositive : 0 < step)

theorem xiNativeSupTransition_power_norm_le_one (jumps : ℕ) :
    ‖xiNativeSupTransition system rulesConnected level ^ jumps‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro values
  simpa only [one_mul] using PoissonizedWalk.contraction_power_apply_le
    (xiNativeSupTransition system rulesConnected level)
    (xiNativeSupTransition_norm_le_one system rulesConnected level) jumps values

theorem xiNativeSupTransition_floor_error_after_smoothing
    (time : ℝ) (timeNonnegative : 0 ≤ time) (forcing : XiVtx system level → ℝ) :
    let smoothed := xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive forcing
    ‖(xiNativeSupTransition system rulesConnected level ^
        Nat.floor (time * xiNativeFiniteJumpRate system level resistanceRate normalization)) forcing -
      xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time forcing‖ ≤
      2 * ‖forcing - smoothed‖ +
        ((Real.sqrt (Nat.floor (time * xiNativeFiniteJumpRate system level resistanceRate normalization)) + 1) /
          xiNativeFiniteJumpRate system level resistanceRate normalization) * (2 * ‖forcing‖ / step) := by
  dsimp only
  apply contraction_comparison_after_smoothing _ _
    (xiNativeSupTransition_power_norm_le_one system rulesConnected level _)
    (xiNativeSupSemigroup_norm_le_one system rulesConnected level resistanceRate normalization
      ratePositive.le normalizationPositive.le time timeNonnegative)
  have jumpPositive := xiNativeFiniteJumpRate_positive system mass level resistanceRate normalization
    ratePositive normalizationPositive
  have comparison := xiNativeSupTransition_floor_poisson_comparison system rulesConnected level
    (xiNativeFiniteJumpRate system level resistanceRate normalization) jumpPositive time timeNonnegative
    (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive forcing)
  have generatorBound := xiNativeFiniteResolvent_sup_generator_bound system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent mass level resistanceRate normalization ratePositive.le normalizationPositive.le
    step stepPositive forcing
  have coefficientNonnegative : 0 ≤
      (Real.sqrt (Nat.floor (time * xiNativeFiniteJumpRate system level resistanceRate normalization)) + 1) /
        xiNativeFiniteJumpRate system level resistanceRate normalization := by positivity
  have estimate := comparison.trans (mul_le_mul_of_nonneg_left generatorBound coefficientNonnegative)
  simpa only [xiNativeSupSemigroup, xiNativeSupGenerator, smul_smul, neg_mul,
    xiNativeSupResolvent_apply] using estimate

theorem xiNativeSupTransition_absolute_floor_error_after_smoothing
    (first second : ℝ) (firstNonnegative : 0 ≤ first) (ordered : first ≤ second)
    (forcing : XiVtx system level → ℝ) :
    let smoothed := xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive forcing
    ‖(xiNativeSupTransition system rulesConnected level ^
        (Nat.floor (second * xiNativeFiniteJumpRate system level resistanceRate normalization) -
          Nat.floor (first * xiNativeFiniteJumpRate system level resistanceRate normalization))) forcing -
      xiNativeSupSemigroup system rulesConnected level resistanceRate normalization (second - first) forcing‖ ≤
      2 * ‖forcing - smoothed‖ +
        ((Real.sqrt (Nat.floor ((second - first) * xiNativeFiniteJumpRate system level resistanceRate normalization)) + 2) /
          xiNativeFiniteJumpRate system level resistanceRate normalization) * (2 * ‖forcing‖ / step) := by
  dsimp only
  apply contraction_comparison_after_smoothing _ _
    (xiNativeSupTransition_power_norm_le_one system rulesConnected level _)
    (xiNativeSupSemigroup_norm_le_one system rulesConnected level resistanceRate normalization
      ratePositive.le normalizationPositive.le (second - first) (sub_nonneg.mpr ordered))
  have jumpPositive := xiNativeFiniteJumpRate_positive system mass level resistanceRate normalization
    ratePositive normalizationPositive
  have comparison := xiNativeSupTransition_absolute_floor_increment_poisson_comparison system rulesConnected level
    (xiNativeFiniteJumpRate system level resistanceRate normalization) jumpPositive first second firstNonnegative ordered
    (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive forcing)
  have generatorBound := xiNativeFiniteResolvent_sup_generator_bound system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent mass level resistanceRate normalization ratePositive.le normalizationPositive.le
    step stepPositive forcing
  have coefficientNonnegative : 0 ≤
      (Real.sqrt (Nat.floor ((second - first) * xiNativeFiniteJumpRate system level resistanceRate normalization)) + 2) /
        xiNativeFiniteJumpRate system level resistanceRate normalization := by positivity
  have estimate := comparison.trans (mul_le_mul_of_nonneg_left generatorBound coefficientNonnegative)
  simpa only [xiNativeSupSemigroup, xiNativeSupGenerator, smul_smul, neg_mul,
    xiNativeSupResolvent_apply] using estimate

end
end EIGS

#print axioms EIGS.xiNativeSupTransition_power_norm_le_one
#print axioms EIGS.xiNativeSupTransition_floor_error_after_smoothing
#print axioms EIGS.xiNativeSupTransition_absolute_floor_error_after_smoothing
