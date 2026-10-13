import RequestProject.Section31.EIGSNativeSupResolventOperator
import RequestProject.Section31.EIGSNativeSemigroupConvergence

/-! Actual native finite exponentials on vertex functions with the supremum
norm. Poisson weights prove contraction. The concrete generator-resolvent
identities then give vectorwise Yosida comparisons, including resolvent
smoothing, without a bound on the finite generator's operator norm. -/

namespace EIGS

open IGS.Sec31 MeasureTheory
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

noncomputable local instance : NormedAlgebra ℚ
    ((XiVtx system level → ℝ) →L[ℝ] (XiVtx system level → ℝ)) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

def xiNativeSupSemigroup (time : ℝ) :
    (XiVtx system level → ℝ) →L[ℝ] (XiVtx system level → ℝ) :=
  NormedSpace.exp ((-time) • xiNativeSupGenerator system rulesConnected level resistanceRate normalization)

include rateNonnegative normalizationNonnegative in
theorem xiNativeSupSemigroup_norm_le_one (time : ℝ) (timeNonnegative : 0 ≤ time) :
    ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time‖ ≤ 1 := by
  have rateNonnegative' := xiNativeFiniteJumpRate_nonnegative system level resistanceRate normalization
    rateNonnegative normalizationNonnegative
  have poissonBound := PoissonizedWalk.Banach.exponential_norm_le
    (xiNativeSupTransition system rulesConnected level)
    (xiNativeSupTransition_norm_le_one system rulesConnected level)
    (time * xiNativeFiniteJumpRate system level resistanceRate normalization)
    (mul_nonneg timeNonnegative rateNonnegative')
  simpa only [xiNativeSupSemigroup, xiNativeSupGenerator, smul_smul, neg_mul] using poissonBound

theorem xiNativeSupSemigroup_yosida_error
    (time : ℝ) (timeNonnegative : 0 ≤ time) (values : XiVtx system level → ℝ) :
    ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time values -
      BoundedYosida.semigroup
        (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)
        step time values‖ ≤
    time * ‖xiNativeSupGenerator system rulesConnected level resistanceRate normalization values -
      xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
        (xiNativeSupGenerator system rulesConnected level resistanceRate normalization values)‖ := by
  have comparison := BoundedSemigroupComparison.norm_exp_apply_sub_le
    (xiNativeSupGenerator system rulesConnected level resistanceRate normalization)
    (BoundedYosida.generator
      (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive) step)
    (xiNativeSupGenerator_yosida_commute system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)
    (xiNativeSupSemigroup_norm_le_one system rulesConnected level resistanceRate normalization
      rateNonnegative normalizationNonnegative)
    (BoundedYosida.semigroup_norm_le_one _
      (xiNativeSupResolvent_norm_le_one system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)
      step stepPositive)
    time timeNonnegative values
  simpa only [xiNativeSupSemigroup, BoundedYosida.semigroup,
    xiNativeSupYosidaGenerator_apply system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive] using comparison

theorem xiNativeSupSemigroup_yosida_smoothed_error
    (smoothingStep : ℝ) (smoothingPositive : 0 < smoothingStep)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (forcing : XiVtx system level → ℝ) :
    let smoothed := xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative smoothingStep smoothingPositive forcing
    let generatorValues := smoothingStep⁻¹ • (forcing - smoothed)
    ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time smoothed -
      BoundedYosida.semigroup
        (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)
        step time smoothed‖ ≤
      time * ‖generatorValues - xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive generatorValues‖ := by
  dsimp only
  simpa only [xiNativeSupGenerator_resolvent_graph system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative smoothingStep smoothingPositive] using
    xiNativeSupSemigroup_yosida_error system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive time timeNonnegative
      (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative smoothingStep smoothingPositive forcing)

theorem xiNativeSupSemigroup_yosida_error_after_smoothing
    (smoothingStep : ℝ) (smoothingPositive : 0 < smoothingStep)
    (time : ℝ) (timeNonnegative : 0 ≤ time) (forcing : XiVtx system level → ℝ) :
    let smoothed := xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative smoothingStep smoothingPositive forcing
    let generatorValues := smoothingStep⁻¹ • (forcing - smoothed)
    ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time forcing -
      BoundedYosida.semigroup
        (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)
        step time forcing‖ ≤
      2 * ‖forcing - smoothed‖ +
        time * ‖generatorValues - xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive generatorValues‖ := by
  let smoothed := xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative smoothingStep smoothingPositive forcing
  let generatorValues := smoothingStep⁻¹ • (forcing - smoothed)
  change ‖xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time forcing -
    BoundedYosida.semigroup
      (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)
      step time forcing‖ ≤ 2 * ‖forcing - smoothed‖ +
        time * ‖generatorValues - xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive generatorValues‖
  exact contraction_comparison_after_smoothing
    (xiNativeSupSemigroup system rulesConnected level resistanceRate normalization time)
    (BoundedYosida.semigroup
      (xiNativeSupResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive) step time)
    (xiNativeSupSemigroup_norm_le_one system rulesConnected level resistanceRate normalization
      rateNonnegative normalizationNonnegative time timeNonnegative)
    (BoundedYosida.semigroup_norm_le_one _
      (xiNativeSupResolvent_norm_le_one system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)
      step stepPositive time timeNonnegative)
    forcing smoothed _
    (xiNativeSupSemigroup_yosida_smoothed_error system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      smoothingStep smoothingPositive time timeNonnegative forcing)

end
end EIGS

#print axioms EIGS.xiNativeSupSemigroup_norm_le_one
#print axioms EIGS.xiNativeSupSemigroup_yosida_error
#print axioms EIGS.xiNativeSupSemigroup_yosida_smoothed_error
#print axioms EIGS.xiNativeSupSemigroup_yosida_error_after_smoothing
