import RequestProject.Section31.EIGSNativeDiscreteContraction
import RequestProject.Section31.EIGSNativeSemigroupComparison

/-! Resolvent smoothing bounds the actual generator independently of graph
size. This is the estimate used to remove Poissonization on varying L² data. -/

namespace EIGS

open MeasureTheory
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
    (step : ℝ) (stepPositive : 0 < step)

theorem xiNativeFiniteGenerator_resolvent_norm_le
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    ‖xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization
      (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization ratePositive.le normalizationPositive.le
        step stepPositive values)‖ ≤ (2 / step) * ‖values‖ := by
  rw [xiNativeFiniteGenerator_resolvent_graph system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level resistanceRate normalization ratePositive.le
    normalizationPositive.le step stepPositive, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr stepPositive)]
  have normBound : ‖xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level resistanceRate normalization ratePositive.le
      normalizationPositive.le step stepPositive values‖ ≤ ‖values‖ :=
    ((xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level resistanceRate normalization ratePositive.le
      normalizationPositive.le step stepPositive).1 values).2.2
  calc
    _ ≤ step⁻¹ * (‖values‖ + ‖xiNativeFiniteResolvent system rulesConnected rulesLoopless
        rulesUnique plantingNonadjacent mass level resistanceRate normalization ratePositive.le
        normalizationPositive.le step stepPositive values‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr stepPositive.le)
    _ ≤ step⁻¹ * (‖values‖ + ‖values‖) :=
      mul_le_mul_of_nonneg_left (add_le_add_right normBound _) (inv_nonneg.mpr stepPositive.le)
    _ = (2 / step) * ‖values‖ := by ring

end
end EIGS

#print axioms EIGS.xiNativeFiniteGenerator_resolvent_norm_le
