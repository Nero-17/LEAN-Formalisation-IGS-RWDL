import RequestProject.Section31.EIGSNativeDiscreteResolventEstimate
import RequestProject.Section31.PoissonizedWalkTimeRounding

/-! Integer-time comparison at the original paper's actual time scale. -/

namespace EIGS
open MeasureTheory Filter Topology
noncomputable section

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)
    (resistanceRate normalization : ℝ)
    (ratePositive : 0 < resistanceRate) (normalizationPositive : 0 < normalization)

include rulesLoopless rulesUnique plantingNonadjacent ratePositive normalizationPositive in
theorem xiNativeRandomWalk_floor_comparison
    (time : ℝ) (timeNonnegative : 0 ≤ time)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    ‖(xiNativeRandomWalk system rulesConnected mass level ^
        Nat.floor (time * xiNativeFiniteJumpRate system level resistanceRate normalization)) values -
      xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time values‖ ≤
      ((Real.sqrt (Nat.floor (time * xiNativeFiniteJumpRate system level resistanceRate normalization)) + 1) /
        xiNativeFiniteJumpRate system level resistanceRate normalization) *
      ‖xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization values‖ := by
  have comparison := IGS.Sec31.PoissonizedWalk.discrete_power_floor_poisson_comparison
    (xiNativeRandomWalk system rulesConnected mass level)
    (xiNativeRandomWalk_norm_le_one system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level)
    (xiNativeFiniteJumpRate system level resistanceRate normalization)
    (xiNativeFiniteJumpRate_positive system mass level resistanceRate normalization
      ratePositive normalizationPositive) time timeNonnegative values
  simpa only [xiNativeFiniteSemigroup, xiNativeFiniteGenerator_eq_jumpRate,
    smul_smul, neg_mul] using comparison

theorem xiNativeRandomWalk_floor_resolvent_comparison
    (step : ℝ) (stepPositive : 0 < step) (time : ℝ) (timeNonnegative : 0 ≤ time)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    ‖(xiNativeRandomWalk system rulesConnected mass level ^
        Nat.floor (time * xiNativeFiniteJumpRate system level resistanceRate normalization))
        (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive values) -
      xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time
        (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization ratePositive.le normalizationPositive.le step stepPositive values)‖ ≤
      ((Real.sqrt (Nat.floor (time * xiNativeFiniteJumpRate system level resistanceRate normalization)) + 1) /
        xiNativeFiniteJumpRate system level resistanceRate normalization) * ((2 / step) * ‖values‖) := by
  apply (xiNativeRandomWalk_floor_comparison system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level resistanceRate normalization ratePositive normalizationPositive
    time timeNonnegative _).trans
  apply mul_le_mul_of_nonneg_left
    (xiNativeFiniteGenerator_resolvent_norm_le system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level resistanceRate normalization ratePositive normalizationPositive
      step stepPositive values)
  exact IGS.Sec31.PoissonizedWalk.rounding_coefficient_nonnegative time _
    (xiNativeFiniteJumpRate_positive system mass level resistanceRate normalization
      ratePositive normalizationPositive)

end
end EIGS

#print axioms EIGS.xiNativeRandomWalk_floor_comparison
#print axioms EIGS.xiNativeRandomWalk_floor_resolvent_comparison
