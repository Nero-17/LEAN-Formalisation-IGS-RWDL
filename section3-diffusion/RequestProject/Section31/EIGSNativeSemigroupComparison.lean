import RequestProject.Section31.EIGSNativeSemigroup
import RequestProject.Section31.EIGSNativeYosidaConvergence
import RequestProject.Section31.BoundedSemigroupComparison

/-! Comparison of the actual native finite random-walk semigroup with its
actual resolvent Yosida exponential. All commutation identities are derived
from the concrete finite resolvent equation and uniqueness. -/

namespace EIGS

open MeasureTheory IGS.Sec31

noncomputable section

set_option maxHeartbeats 2400000

variable {K : ℕ} (system : EIGSData K)
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
    (Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ]
      Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

/-- The concrete resolvent is also a right inverse of `I + step • A`. -/
theorem xiNativeFiniteResolvent_inverse
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (values + step • xiNativeFiniteGenerator system rulesConnected mass level
        resistanceRate normalization values) = values := by
  exact (((xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level resistanceRate normalization rateNonnegative
    normalizationNonnegative step stepPositive).1 _).2.1 values rfl).symm

/-- Applying the actual generator to the finite resolvent equation proves
commutation, with no independent commutation premise. -/
theorem xiNativeFiniteGenerator_resolvent_apply
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization
      (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive values) =
    xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization values) := by
  let generator := xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization
  let resolvent := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
  have solutionIdentity : resolvent values + step • generator (resolvent values) = values :=
    ((xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level resistanceRate normalization rateNonnegative
      normalizationNonnegative step stepPositive).1 values).1
  have generatorEquation : generator (resolvent values) +
      step • generator (generator (resolvent values)) = generator values := by
    simpa only [map_add, map_smul] using congrArg generator solutionIdentity
  exact ((xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level resistanceRate normalization rateNonnegative
    normalizationNonnegative step stepPositive).1 (generator values)).2.1 _ generatorEquation

theorem xiNativeFiniteGenerator_resolvent_commute :
    Commute (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization)
      (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive) := by
  apply (commute_iff_eq _ _).mpr
  apply ContinuousLinearMap.ext
  intro values
  exact xiNativeFiniteGenerator_resolvent_apply system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level resistanceRate normalization rateNonnegative
    normalizationNonnegative step stepPositive values

/-- The resolvent defect is the actual generator applied to the solution. -/
theorem xiNativeFiniteResolvent_defect
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    values - xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive values =
    step • xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization
      (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive values) := by
  apply sub_eq_iff_eq_add.mpr
  exact (((xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level resistanceRate normalization rateNonnegative
    normalizationNonnegative step stepPositive).1 values).1).symm.trans (add_comm _ _)

/-- A forcing graph identity, suitable for later resolvent-smoothed data. -/
theorem xiNativeFiniteGenerator_resolvent_graph
    (forcing : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization
      (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing) =
    step⁻¹ • (forcing - xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing) := by
  rw [xiNativeFiniteResolvent_defect system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive forcing,
    smul_smul, inv_mul_cancel₀ stepPositive.ne', one_smul]

/-- The actual finite Yosida operator equals the concrete resolvent followed
by the actual finite generator. -/
theorem xiNativeFiniteYosidaGenerator_apply
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    BoundedYosida.generator
      (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive) step values =
    xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive
      (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization values) := by
  change step⁻¹ • (values - xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive values) = _
  rw [← xiNativeFiniteGenerator_resolvent_graph system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive values]
  exact xiNativeFiniteGenerator_resolvent_apply system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive values

/-- Commutation of the actual finite generator and its actual Yosida operator. -/
theorem xiNativeFiniteGenerator_yosida_commute :
    Commute (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization)
      (BoundedYosida.generator
        (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive) step) := by
  exact ((Commute.one_right _).sub_right
    (xiNativeFiniteGenerator_resolvent_commute system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)).smul_right step⁻¹

/-- Both semigroups in this estimate are the genuine exponentials of the
concrete native finite operators. The resolvent defect controls their error
on the vector itself, with no bound on the finite generator's operator norm. -/
theorem xiNativeFiniteSemigroup_yosida_error
    (time : ℝ) (timeNonnegative : 0 ≤ time)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    ‖xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time values -
      xiNativeYosidaSemigroup system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level
        resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive time values‖ ≤
    time * ‖(1 - xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)
      (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization values)‖ := by
  have comparison := BoundedSemigroupComparison.norm_exp_apply_sub_le
    (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization)
    (BoundedYosida.generator
      (xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level
        resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive) step)
    (xiNativeFiniteGenerator_yosida_commute system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive)
    (xiNativeFiniteSemigroup_norm system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative)
    (BoundedYosida.semigroup_norm_le_one _
      (xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level
        resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive).2 step stepPositive)
    time timeNonnegative values
  simpa only [xiNativeFiniteSemigroup, xiNativeYosidaSemigroup, BoundedYosida.semigroup,
    xiNativeFiniteYosidaGenerator_apply system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step stepPositive,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using comparison

end
end EIGS

#print axioms EIGS.xiNativeFiniteResolvent_inverse
#print axioms EIGS.xiNativeFiniteGenerator_resolvent_apply
#print axioms EIGS.xiNativeFiniteGenerator_resolvent_commute
#print axioms EIGS.xiNativeFiniteResolvent_defect
#print axioms EIGS.xiNativeFiniteGenerator_resolvent_graph
#print axioms EIGS.xiNativeFiniteYosidaGenerator_apply
#print axioms EIGS.xiNativeFiniteGenerator_yosida_commute
#print axioms EIGS.xiNativeFiniteSemigroup_yosida_error
